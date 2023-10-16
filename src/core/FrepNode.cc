/*
 *  OpenSCAD (www.openscad.org)
 *  Copyright (C) 2009-2011 Clifford Wolf <clifford@clifford.at> and
 *                          Marius Kintel <marius@kintel.net>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  As a special exception, you have permission to link this program
 *  with the CGAL library and distribute executables, as long as you
 *  follow the requirements of the GNU GPL in regard to all of the
 *  software in the executable aside from CGAL.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 */

#include "FrepNode.h"
#ifdef ENABLE_PYTHON
#include "pylibfive.h"
#endif

#include "module.h"
#include "ModuleInstantiation.h"
#include "Children.h"
#include "Parameters.h"
#include "printutils.h"
#include "io/fileutils.h"
#include "Builtins.h"
#include "handle_dep.h"
#include "degree_trig.h"



#include <cmath>
#include <sstream>

#include "libfive/render/brep/dc/dc_mesher.hpp"
#include "libfive/render/brep/dc/dc_worker_pool.hpp"
#include "libfive/render/brep/region.hpp"
#include "libfive/render/brep/mesh.hpp"

#include <hash.h>
#include <unordered_set>


using namespace libfive;

#define BUCKET 8


// 3D Map stuff
//
class Map3DTree
{
	public:
		Map3DTree(void);
		int ind[8]; // 8 octants, intially -1
		Vector3d pts[BUCKET];
		int ptsind[BUCKET];
		int ptlen; 
	// else ptlen=-1-> inds gelten
	// else pts gelten
};

class Map3D
{
	public:
		Map3D(Vector3d min, Vector3d max);
		void add(Vector3d pt, int ind);
		void del(Vector3d pt);
		int find(Vector3d pt, double r,std::vector<Vector3d> &result,std::vector<int> &resultind,int maxresult);
		void dump_hier(int ind, int hier,float minx, float miny, float minz, float maxx, float maxy, float maxz);
		void dump();
	private:
		void add_sub(int ind,Vector3d min, Vector3d max, Vector3d pt,int ptind, int disable_local_num);
		void find_sub(int ind, double minx, double miny, double minz, double maxx, double maxy, double maxz,Vector3d pt, double r,std::vector<Vector3d> &result,std::vector<int> &resultind,int maxresult);
		Vector3d min, max;
		std::vector<Map3DTree> items;
};

Map3DTree::Map3DTree(void) {
	for(int i=0;i<8;ind[i++]=-1);
	ptlen=0;
}

Map3D::Map3D(Vector3d min, Vector3d max) {
	this->min=min;
	this->max=max;
}
void Map3D::add_sub(int ind, Vector3d min, Vector3d max,Vector3d pt, int ptind, int disable_local_num) {
	int indnew;
	int corner;
	Vector3d mid;
	do {
		if(items[ind].ptlen >= 0 && disable_local_num != ind) {
			if(items[ind].ptlen < BUCKET) {
				for(int i=0;i<items[ind].ptlen;i++)
					if(items[ind].pts[i] == pt) return;
				items[ind].pts[items[ind].ptlen]=pt;
				items[ind].ptsind[items[ind].ptlen]=ptind;
				items[ind].ptlen++;
				return;
			} else {  
				for(int i=0;i<items[ind].ptlen;i++) {
					add_sub(ind, min, max,items[ind].pts[i],ptind,ind);
				}
				items[ind].ptlen=-1;
				// run through
			} 
		}
		mid[0]=(min[0]+max[0])/2.0;
		mid[1]=(min[1]+max[1])/2.0;
		mid[2]=(min[2]+max[2])/2.0;
		corner=(pt[0]>=mid[0]?1:0)+(pt[1]>=mid[1]?2:0)+(pt[2]>=mid[2]?4:0);
		indnew=items[ind].ind[corner];
		if(indnew == -1) {
			indnew=items.size();
			items.push_back(Map3DTree());
			items[ind].ind[corner]=indnew;					
		}
		if(corner&1) min[0]=mid[0]; else max[0]=mid[0];
		if(corner&2) min[1]=mid[1]; else max[1]=mid[1];
		if(corner&4) min[2]=mid[2]; else max[2]=mid[2];
		ind=indnew;
	}
	while(1);

}
void Map3D::add(Vector3d pt, int ind) { 
	if(items.size() == 0) {
		items.push_back(Map3DTree());
		items[0].pts[0]=pt;
		items[0].ptsind[0]=ind;
		items[0].ptlen++;
		return;
	}
	add_sub(0,this->min, this->max, pt,ind,-1);
}

void Map3D::del(Vector3d pt) {
	int ind=0;
	int corner;
	Vector3d min=this->min;
	Vector3d max=this->max;
	Vector3d mid;
	printf("Deleting %g/%g/%g\n",pt[0], pt[1], pt[2]);
	while(ind != -1) {
		for(int i=0;i<items[ind].ptlen;i++) {
			if(items[ind].pts[i]==pt) {
				for(int j=i+1;j<items[ind].ptlen;j++)
					items[ind].pts[j-1]=items[ind].pts[j];
				items[ind].ptlen--;
				return;
			}
			// was wenn leer wird dnn sind ind immer noch -1
		}
		mid[0]=(min[0]+max[0])/2.0;
		mid[1]=(min[1]+max[1])/2.0;
		mid[2]=(min[2]+max[2])/2.0;
		corner=(pt[0]>mid[0]?1:0)+(pt[1]>mid[1]?2:0)+(pt[2]>mid[2]?4:0);
		printf("corner=%d\n",corner);
		ind=items[ind].ind[corner];
		if(corner&1) min[0]=mid[0]; else max[0]=mid[0];
		if(corner&2) min[1]=mid[1]; else max[1]=mid[1];
		if(corner&4) min[2]=mid[2]; else max[2]=mid[2];
	}
}

void Map3D::find_sub(int ind, double minx, double miny, double minz, double maxx, double maxy, double maxz, Vector3d pt, double r,std::vector<Vector3d> &result,std::vector<int> &resultind, int maxresult){
	if(ind == -1) return;
	if(this->items[ind].ptlen > 0){
		for(int i=0;i<this->items[ind].ptlen;i++) {
			if((this->items[ind].pts[i]-pt).norm() < r) {
				result.push_back(this->items[ind].pts[i]);
				resultind.push_back(this->items[ind].ptsind[i]);
			}
			if(result.size() >= maxresult) return;
		}
		return;
	}
	double midx,midy, midz;
//	printf("find_sub ind=%d %g/%g/%g - %g/%g/%g\n",ind, minx, miny,  minz, maxx, maxy, maxz );
	midx=(minx+maxx)/2.0;
	midy=(miny+maxy)/2.0;
	midz=(minz+maxz)/2.0;
	if(result.size() >= maxresult) return;
	if( pt[2]+r >= minz && pt[0]-r < midz ) {
		if( pt[1]+r >= miny && pt[0]-r < midy) {
			if(pt[0]+r >= minx && pt[0]-r < midx ) find_sub(this->items[ind].ind[0],minx, miny, minz, midx, midy, midz,pt,r,result,resultind, maxresult);
			if(pt[0]+r >= midx && pt[0]-r < maxx ) find_sub(this->items[ind].ind[1],midx, miny, minz, maxx, midy, midz,pt,r,result,resultind, maxresult);
		}
		if( pt[1]+r >= midy && pt[0]-r < maxy) {
			if(pt[0]+r >= minx && pt[0]-r < midx ) find_sub(this->items[ind].ind[2],minx, midy, minz, midx, maxy, midz,pt,r,result,resultind, maxresult);
			if(pt[0]+r >= midx && pt[0]-r < maxx ) find_sub(this->items[ind].ind[3],midx, midy, minz, maxx, maxy, midz,pt,r,result,resultind, maxresult);
		}
	}
	if( pt[2]+r >= midz && pt[0]-r < maxz ) {
		if( pt[1]+r >= miny && pt[0]-r < midy) {
			if(pt[0]+r >= minx && pt[0]-r < midx ) find_sub(this->items[ind].ind[4],minx, miny, midz, midx, midy, maxz,pt,r,result,resultind, maxresult);
			if(pt[0]+r >= midx && pt[0]-r < maxx ) find_sub(this->items[ind].ind[5],midx, miny, midz, maxx, midy, maxz,pt,r,result,resultind, maxresult);
		}
		if( pt[1]+r >= midy && pt[0]-r < maxy) {
			if(pt[0]+r >= minx && pt[0]-r < midx ) find_sub(this->items[ind].ind[6],minx, midy, midz, midx, maxy, maxz,pt,r,result,resultind, maxresult);
			if(pt[0]+r >= midx && pt[0]-r < maxx ) find_sub(this->items[ind].ind[7],midx, midy, midz, maxx, maxy, maxz,pt,r,result,resultind, maxresult);
		}
	}

}
int Map3D::find(Vector3d pt, double r,std::vector<Vector3d> &result, std::vector<int> &resultind, int maxresult){
	int results=0;
	if(items.size() == 0) return results;
	result.clear();
	resultind.clear();
	find_sub(0,this->min[0], this->min[1], this->min[2], this->max[0], this->max[1], this->max[2], pt,r,result, resultind, maxresult);
	return result.size();
}

void Map3D::dump_hier(int i, int hier, float minx, float miny, float minz, float maxx, float maxy, float maxz) {
	for(int i=0;i<hier;i++) printf("  ");
	printf("%d inds ",i);
	for(int j=0;j<8;j++) printf("%d ",items[i].ind[j]);
	printf("pts ");
	for(int j=0;j<items[i].ptlen;j++) printf("%g/%g/%g ",items[i].pts[j][0],items[i].pts[j][1],items[i].pts[j][2]);

	float midx, midy, midz;
	midx=(minx+maxx)/2.0;
	midy=(miny+maxy)/2.0;
	midz=(minz+maxz)/2.0;
	printf(" (%g/%g/%g - %g/%g/%g)\n", minx, miny, minz, maxx, maxy, maxz);
	if(items[i].ind[0] != -1) dump_hier(items[i].ind[0],hier+1,minx,miny, minz, midx, midy, midz);
	if(items[i].ind[1] != -1) dump_hier(items[i].ind[1],hier+1,midx,miny, minz, maxx, midy, midz);
	if(items[i].ind[2] != -1) dump_hier(items[i].ind[2],hier+1,minx,midy, minz, midx, maxy, midz);
	if(items[i].ind[3] != -1) dump_hier(items[i].ind[3],hier+1,midx,midy, minz, maxx, maxy, midz);
	if(items[i].ind[4] != -1) dump_hier(items[i].ind[4],hier+1,minx,miny, midz, midx, midy, maxz);
	if(items[i].ind[5] != -1) dump_hier(items[i].ind[5],hier+1,midx,miny, midz, maxx, midy, maxz);
	if(items[i].ind[6] != -1) dump_hier(items[i].ind[6],hier+1,minx,midy, midz, midx, maxy, maxz);
	if(items[i].ind[7] != -1) dump_hier(items[i].ind[7],hier+1,midx,midy, midz, maxx, maxy, maxz);
}
void Map3D::dump(void) {
	dump_hier(0,0,min[0],min[1],min[2],max[0], max[1],max[2]);
}

/*
int main(void)
{
	char *line=NULL;
	size_t linelen;
	Vector3d ptmin(-10,-10,-10);
	Vector3d ptmax(10,10,10);
	Vector3d pt;
	std::vector<Vector3d> result;
	Map3D map(ptmin, ptmax);
	for(int i=0;i<8;i++)
	  map.add(Vector3d(1,1,i));
	map.dump();
	do
	{
		printf("> ");
		getline(&line, &linelen, stdin);
		printf("Read: %s\n",line);
//		
		
		if(sscanf(line,"add %lf %lf %lf",&pt[0], &pt[1],&pt[2]) == 3) {
			map.add(pt);
			printf("added \n");
			map.dump();
		}
		if(sscanf(line,"del %lf %lf %lf",&pt[0], &pt[1],&pt[2]) == 3) {
			map.del(pt);
			printf("deleted \n");
			map.dump();
		}
		if(sscanf(line,"find %lf %lf %lf",&pt[0], &pt[1],&pt[2]) == 3) {
			result.clear();
			map.find(pt,0.1,result);
			printf("found:%ld \n",result.size());
			for(unsigned int i=0;i<result.size();i++)
				printf("%g/%g/%g\n",result[i][0],result[i][1],result[i][2]);
			printf("\n");
		}
//		free(line);
	}while(1);

}

*/

typedef struct
{
	Vector3d pos;
	Vector3d norm;
} SDFVertex;

typedef struct 
{
	double ang;
	int ptind;
} SDFCorner ;

typedef struct 
{
	int i[3];
} SDFTriangle ;


double sdf_sphere(Vector3d  pt, double r)
{
	return sqrt(pt[0]*pt[0]+pt[1]*pt[1]+pt[2]*pt[2])-r;
}
double sdf_func(libfive::Tree &tr, Vector3d pt)
{
	libfive_vec3 lvpt;
	Vector3d pt1=pt,pt2=pt;
	double sdf1, sdf2;
	lvpt.x=pt[0];
	lvpt.y=pt[1];
	lvpt.z=pt[2];
//	ArrayEvaluator e((Tree(tr)));
//	double xx =e.value({pt[0], pt[1], pt[2]});
	
	double r=1.4;
	pt1[0] += 1.5;
	pt2[0] -= 1.5;
	sdf1=sdf_sphere(pt1,r);
	sdf2=sdf_sphere(pt2,r);
	return sdf1<sdf2?sdf1:sdf2;
	// ../submodules/libfive/libfive/src/libfive.cpp
	// float libfive_tree_eval_f(libfive_tree t, libfive_vec3 p)
}

Vector3d SDF_calculateNorm(Vector3d v1, double b1, Vector3d v2, double b2, Vector3d v3, double b3)
{
	Vector3d r(0,0,0);
	double c1,c2,c3,n;
	c1=v2[1]*v3[2]-v2[2]*v3[1];
	c2=v2[2]*v3[0]-v2[0]*v3[2];
	c3=v2[0]*v3[1]-v2[1]*v3[0];
	n=v1[0]*c1+v1[1]*c2+v1[2]*c3;
	if(fabs(n) < 1e-9) return r;

	r[0]=(b1*c1+b2*(v1[2]*v3[1]-v1[1]*v3[2])+b3*(v1[1]*v2[2]-v1[2]*v2[1]))/n;
	r[1]=(b1*c2+b2*(v1[0]*v3[2]-v1[2]*v3[0])+b3*(v1[2]*v2[0]-v1[0]*v2[2]))/n;
	r[2]=(b1*c3+b2*(v1[1]*v3[0]-v1[0]*v3[1])+b3*(v1[0]*v2[1]-v1[1]*v2[0]))/n;

	return r;
}
Vector3d SDF_calculateNormComp(libfive::Tree &tr, Vector3d pt, Vector3d diff1)
{
	Vector3d pt1,pt2, pt3;
	double sdf, sdf1, sdf2, sdf3;
	double b1, b2, b3;

	Vector3d diff2(-diff1[2],diff1[0],diff1[1]);
	Vector3d diff3(-diff2[2],diff2[0],diff2[1]);

	sdf=sdf_func(tr,pt);
	pt1=pt-diff1;
	sdf1=sdf_func(tr,pt1);
	b1=(sdf-sdf1)/diff1.norm();

	pt2=pt-diff2;
	sdf2=sdf_func(tr,pt2);
	b2=(sdf-sdf2)/diff2.norm();

	pt3=pt-diff3;
	sdf3=sdf_func(tr,pt3);
	b3=(sdf-sdf3)/diff3.norm();

	Vector3d norm =SDF_calculateNorm(Vector3d(1,0,0),b1, Vector3d(0,1,0),b2, Vector3d(0,0,1), b3);
//	printf("norm is %g/%g/%g\n",norm[0],norm[1],norm[2]);
	norm.normalize();
//	printf("recalcnorm done\n");
	return norm;
}

int SDF_align(libfive::Tree &tr,SDFVertex  &vert,double tol) {
//	printf("align pt :%g/%g/%g norm:%g/%g/%g\n",vert.pos[0],vert.pos[1],vert.pos[2], vert.norm[0],vert.norm[1],vert.norm[2]);
	if(vert.norm.norm() < 1e-9){
		vert.norm=SDF_calculateNormComp(tr,vert.pos,Vector3d(0.01,0,0));
		vert.norm.normalize();
	}
	double sdf = sdf_func(tr,vert.pos);
	int fails=0;
	do
	{
		// now move the pt
		Vector3d pt_bak=vert.pos;
		vert.pos -= sdf * vert.norm;
//		printf("pt is %g/%g/%g\n",vert.pos[0],vert.pos[1],vert.pos[2]);
		double sdftest = sdf_func(tr,vert.pos);
//		printf("sdftest is %g\n",sdftest);
		if(sdftest > 10) exit(1);
		if(isinf(sdftest)) exit(1);
		double b=(sdf - sdftest)/sdf;
//		printf("b=%g\n",b);
		if(fabs(b) < 0.1) fails++;
		else if(fabs(sdftest) > fabs(sdf)) fails++;
		else fails=0;
		if(fails == 3) {
			return 1;
		}
//		if(b <  0.9) { 
//			vert.pos=pt_bak;
//			norm=SDF_calculateNormComp(vert.pos,vert.norm);
//			norm.normalize();
//		} else {
			sdf=sdftest;
//		}
	} while(fabs(sdf) > tol);
	return 0;
}

void debug_point(PolySet *p, SDFVertex &vert) 
{
	double size=0.3;
	Vector3d tmp(0,1,0),xdir, ydir;
	// zdir = vert.norm
	xdir=vert.norm.cross(tmp);
	ydir=vert.norm.cross(xdir);
	xdir.normalize();
	ydir.normalize();
			

	Vector3d p1,p2,p3;
	p1=vert.pos+(vert.norm+xdir)*size;

	p->append_poly(3);
	tmp=vert.pos; p->append_vertex(tmp[0],tmp[1],tmp[2]);
	tmp=vert.pos+(vert.norm-xdir*0.5+ydir*0.866)*size; p->append_vertex(tmp[0],tmp[1],tmp[2]);
	tmp=vert.pos+(vert.norm+xdir)*size; p->append_vertex(tmp[0],tmp[1],tmp[2]);

	p->append_poly(3);
	tmp=vert.pos; p->append_vertex(tmp[0],tmp[1],tmp[2]);
	tmp=vert.pos+(vert.norm-xdir*0.5-ydir*0.866)*size; p->append_vertex(tmp[0],tmp[1],tmp[2]);
	tmp=vert.pos+(vert.norm-xdir*0.5+ydir*0.866)*size; p->append_vertex(tmp[0],tmp[1],tmp[2]);

	p->append_poly(3);
	tmp=vert.pos; p->append_vertex(tmp[0],tmp[1],tmp[2]);
	tmp=vert.pos+(vert.norm+xdir)*size; p->append_vertex(tmp[0],tmp[1],tmp[2]);
	tmp=vert.pos+(vert.norm-xdir*0.5-ydir*0.866)*size; p->append_vertex(tmp[0],tmp[1],tmp[2]);
}

#define myminax(a,b) a<b?a:b

void draw_line(Vector3d  p1, Vector3d p2,std::vector<SDFVertex> &pts,std::vector<SDFTriangle> &tris)
{
	Vector3d  n=(p2-p1).normalized();
	Vector3d ydir=Vector3d(1,0,0).cross(n).normalized();
	Vector3d xdir=ydir.cross(n).normalized();
	xdir *= 0.01;
	ydir *= 0.01;
	std::vector<int> inds;
	SDFTriangle tri;
	for(int i=0;i<8;i++)
	{
		SDFVertex pt;
		pt.pos=(i&4)?p2:p1;
		pt.pos += (i&1)?xdir:-xdir;
		pt.pos += (i&2)?ydir:-ydir;
		inds.push_back(pts.size());
		pts.push_back(pt);
	}
	tri.i[0]=inds[0]; tri.i[1]=inds[1]; tri.i[2]=inds[5]; tris.push_back(tri);
	tri.i[0]=inds[0]; tri.i[1]=inds[5]; tri.i[2]=inds[4]; tris.push_back(tri);
	tri.i[0]=inds[1]; tri.i[1]=inds[3]; tri.i[2]=inds[7]; tris.push_back(tri);
	tri.i[0]=inds[1]; tri.i[1]=inds[7]; tri.i[2]=inds[5]; tris.push_back(tri);
	tri.i[0]=inds[3]; tri.i[1]=inds[2]; tri.i[2]=inds[6]; tris.push_back(tri);
	tri.i[0]=inds[3]; tri.i[1]=inds[2]; tri.i[2]=inds[7]; tris.push_back(tri);
	tri.i[0]=inds[2]; tri.i[1]=inds[0]; tri.i[2]=inds[4]; tris.push_back(tri);
	tri.i[0]=inds[2]; tri.i[1]=inds[4]; tri.i[2]=inds[6]; tris.push_back(tri);
}

PolySet *MySDF(libfive::Tree &tr,Vector3d pmin, Vector3d pmax,double tol)
{
	Vector3d xdir(1,0,0),ydir(0,1,0),zdir(0,0,1);
	double res=0.1; // TODO fix
	SDFVertex v;
	std::vector<SDFTriangle> tris;
	SDFTriangle tri;
	printf("own procedure\n");
	std::vector<SDFVertex> pts;
	std::vector<int> perimeter_inds;
	Vector3d pmid; // Calculate mid
	pmid[0]=(pmin[0]+pmax[0])/2.0;
	pmid[1]=(pmin[0]+pmax[1])/2.0;
	pmid[2]=(pmin[0]+pmax[2])/2.0;

	Map3D map3d(pmin, pmax); // Create initial point and assign at as single perimeter point
	v.norm=Vector3d(0,0,0);
	v.pos[0]=pmin[0];  // TODO merhere optionen wenn SDF_align schiegf geht
	v.pos[1]=pmid[0];
	v.pos[2]=pmid[0];
	SDF_align(tr,v ,tol);
	printf("init pos is %g/%g/%g\n",v.pos[0],v.pos[1],v.pos[2]);

	map3d.add(v.pos,pts.size());
	perimeter_inds.push_back(pts.size());
	pts.push_back(v);

	int rounds=0;
	while(perimeter_inds.size() > 0 && rounds < 2) // continue until perimeter is not closed
	{
		printf("%d points in perimeter\n",perimeter_inds.size());
		int baseptind=perimeter_inds[perimeter_inds.size()-1]; // take one perimeter index
		printf("Progressing %d\n",baseptind);

		// find nearby points
		std::vector<Vector3d> result;
		std::vector<int> resultind;
		SDFVertex basept=pts[baseptind];
		map3d.find(basept.pos,res*1.5,result,resultind, 10);
		printf("Points found: %d\n",result.size());

		// filter center point
		std::vector<SDFCorner> corners; 
		SDFCorner corner;
		for(int i=0;i<result.size();i++)
		{
			if(result[i] == basept.pos){
				result.erase(result.begin() + i);
				continue;
			} else {
				corner.ptind=resultind[i];
				corners.push_back(corner);
			}
		}
		printf("%d points founda after filtering\n",corners.size());

		// special case: no points
		if(corners.size() == 0) {
			printf("No neighbor points\n");
			// no neighboring points, create 1st one
			Vector3d newdir;
			newdir=basept.norm.cross(xdir); 
			if(newdir.norm() < 1e-6) newdir=basept.norm.cross(ydir); 
			if(newdir.norm() < 1e-6) newdir=basept.norm.cross(zdir); 
			newdir.normalize();
			printf("newdir is %g/%g/%g\n",newdir[0],newdir[1],newdir[2]);
			SDFVertex newpt;
			newpt.pos=basept.pos+newdir*res;
			newpt.norm=basept.norm;
			SDF_align(tr,newpt ,tol);
			printf("newpos is  %g/%g/%g\n",newpt.pos[0],newpt.pos[1],newpt.pos[2]);

			corner.ptind = pts.size();
			map3d.add(newpt.pos,pts.size());
			pts.push_back(newpt);


			corners.push_back(corner);
		}
		printf("calc other angles\n");
		corners[0].ang=0;
		Vector3d side1=(pts[corners[0].ptind].pos-basept.pos).cross(basept.norm).cross(basept.norm).normalized();
		for(int i=1;i<corners.size();i++) {
			Vector3d side2=(pts[corners[i].ptind].pos-basept.pos).cross(basept.norm).cross(basept.norm).normalized();
			double ang=acos(side1.dot(side2))*180.0/3.1415926;
			if(side1.cross(side2).dot(basept.norm) < 0) ang=-ang;
			while(ang < 0) ang+= 360;
			corners[i].ang=ang;
		}
		
		std::sort(corners.begin(),corners.end(), [](SDFCorner &a, SDFCorner &b){ return a.ang<b.ang; }); // sort corners by angle
		// TODO delete duplicate  corners
		printf("Before add %d edges\n",corners.size());
		for(int i=0;i<corners.size();i++) {
			Vector3d &pt=pts[corners[i].ptind].pos;
			printf("%d ang=%f %d %g/%g/%g \n",i,corners[i].ang,corners[i].ptind,pt[0],pt[1],pt[2]);
		}

		printf("Adding sub edges\n");
		for(int i=0;i<corners.size();i++) // fix angles between edges
		{
			printf("i=%d\n",i);
			double gap=((i==corners.size()-1)?360:corners[i+1].ang)-corners[i].ang;
			printf("gap=%g\n",gap);
			int ranges=ceil(((double)gap/71));
			printf("ranges=%d\n",ranges);
			double baseang=corners[i].ang;
			Vector3d basepos=pts[corners[i].ptind].pos;
			for(int j=0;j<ranges-1;j++) {
				corner.ang=baseang+gap*(j+1)/ranges;
				printf("sub angle = %g\n",corner.ang);
				Transform3d mat=Transform3d::Identity();
				Matrix3d rots=angle_axis_degrees(corner.ang-baseang, basept.norm);
				mat.rotate(rots);

				SDFVertex newpt;
			        newpt.pos = basepos- basept.pos;
			 	newpt.pos = ( mat * newpt.pos) + basept.pos;
				SDF_align(tr,newpt ,tol);

				corner.ptind = pts.size();
				map3d.add(newpt.pos,pts.size());
				pts.push_back(newpt);

				corners.insert(corners.begin()+(i+1),corner); 
				i++;
			}

		}
		printf("Now %d edges\n",corners.size());
		int n=corners.size();
		for(int i=0;i<n;i++) {
			Vector3d &pt=pts[corners[i].ptind].pos;
			printf("%d ang=%f %d %g/%g/%g \n",i,corners[i].ang,corners[i].ptind,pt[0],pt[1],pt[2]);

			// TODO remove calcualte angle between
			Vector3d side1=(pts[corners[i].ptind].pos-basept.pos).cross(basept.norm).cross(basept.norm).normalized();
			Vector3d side2=(pts[corners[(i+1)%n].ptind].pos-basept.pos).cross(basept.norm).cross(basept.norm).normalized();
			double realang=acos(side1.dot(side2))*180.0/3.1415l;
			printf("REal ang is %g\n",realang);
		}


		if(perimeter_inds.size() == 1) {
			perimeter_inds.pop_back();
			for(int i=0;i<n;i++)
			{
				tri.i[0]=baseptind;
				tri.i[1]=corners[i].ptind;
				tri.i[2]=corners[(i+1)%n].ptind;
				tris.push_back(tri);
				perimeter_inds.push_back(corners[i].ptind);
			}
		}
		else
		{
			
			int mode=0;
			std::vector<int> resultchain;
			int newind=0;
			int oldind=0;
			int n=corners.size();
			while(mode != 3) // TODO viel sicherer und eleganter
			{
				printf("mode=%d\n",mode);
				switch(mode) {
					case 0: // inaktiv im neuen
						if(corners[newind].ptind == 5) { mode=1; break;}
						newind++;
						break;
					case 1: // aktiv im neuen
						if(corners[newind].ptind == 1)
						{
							resultchain.push_back(corners[newind].ptind);
							mode=2;oldind=1; break; 
						}
						printf("t %d %d\n",newind, corners[newind].ptind );
						tri.i[0]=baseptind;
						tri.i[1]=corners[newind].ptind;
						tri.i[2]=corners[(newind+1)%n].ptind;
						printf("t %d %d %d\n",tri.i[0],tri.i[1],tri.i[2]);
						tris.push_back(tri);
						resultchain.push_back(corners[newind].ptind);
						newind++;
						break;
					case 2: // aktiv im alten
						if(perimeter_inds[oldind] == 5) { mode=3; break ; }
						resultchain.push_back(perimeter_inds[oldind]);
						oldind++;

				}
			}
			printf("finished\n");
			for(int i=0;i<resultchain.size();i++) printf("%d \n",resultchain[i]);
		}


		rounds++;
	}
	auto p = new PolySet(3, true);

	printf("%d Points and %d Triangles generated\n",pts.size(),tris.size());
	for(int i=0;i<tris.size();i++) {
		p->append_poly(3);
		for(int j=0;j<3;j++) {
			int ind=tris[i].i[j];
			p->append_vertex(pts[ind].pos[0],pts[ind].pos[1],pts[ind].pos[2]);
		}
	}
	return p;
}
#define MY_SDF 
const Geometry *FrepNode::createGeometry() const
{
	PolySet *p;
	std::unique_ptr<Mesh> mesh=NULL;
	libfive::Region<3> reg(
			{this->x1, this->y1, this->z1}, 
			{this->x2, this->y2, this->z2});
	libfive::BRepSettings settings;
	settings.workers = 1;
	settings.min_feature = 1.0 / this->res;

#ifdef ENABLE_PYTHON	
	PyObject *exp = this->expression;
	if(exp == NULL ) return p;

	if(exp->ob_type == &PyLibFiveType) {
		std::vector<Tree *> tree = PyLibFiveObjectToTree(exp);
#ifdef MY_SDF
		p = MySDF(*tree[0],Vector3d(this->x1,this->y1,this->z1), Vector3d(this->x2,this->y2,this->z2),0.001);
#else		
		p = new PolySet(3, true);
		printf("render start\n");
                mesh = Mesh::render(*tree[0], reg ,settings);
		if(mesh != NULL) {
			libfive_tri t;
			for (const auto& t : mesh->branes)
			{
				p->append_poly(3); 
//				printf("p->append_poly(3);\n"); 
				for(int i=0;i<3;i++)
				{
					p->append_vertex(mesh->verts[t[i]].x(), mesh->verts[t[i]].y(), mesh->verts[t[i]].z() );
//					printf("p->append_vertex(%f, %f, %f);\n",mesh->verts[t[i]].x(), mesh->verts[t[i]].y(), mesh->verts[t[i]].z() );
				}
			}
		}
#endif		
	} else if(exp->ob_type == &PyFunction_Type) {
		printf("Python Function!\n");
		mesh = NULL;
	} else { printf("xxx\n"); }
#endif	
/*

	libfive_mesh *mesh = libfive_tree_render_mesh(tree[0],  reg, this->res);
	libfive_tri t;
	for(int i=0;i<mesh->tri_count;i++) 
	{
		t = mesh->tris[i];
		p->append_poly(); 
		p->append_vertex(mesh->verts[t.a].x, mesh->verts[t.a].y, mesh->verts[t.a].z );
		p->append_vertex(mesh->verts[t.b].x, mesh->verts[t.b].y, mesh->verts[t.b].z );
		p->append_vertex(mesh->verts[t.c].x, mesh->verts[t.c].y, mesh->verts[t.c].z );
//		printf("tree: %s\n",libfive_tree_print(tree)); 
#endif	
>>>>>>> 2394429a781c7b1f17da303b9aa2eb2bb3960e71
	}
*/	
	return p;
}


// polyset to SDF converter

void convertToIndex(const PolySet *ps, std::vector<Vector3d> &pointList,  std::vector<intList> &polygons,std::vector<intList>  &pointToFaceInds)
{
  std::unordered_map<Vector3d, int, boost::hash<Vector3d> > pointIntMap;
  intList emptyList;
//  printf("polygons\n");
  for(int i=0;i<ps->polygons.size();i++) {
    Polygon pol = ps->polygons[i];
    intList polygon;
    for(int j=0;j<pol.size(); j++) {
      int ptind=0;
      Vector3d  pt=pol[j];
      if(!pointIntMap.count(pt))
      {
        pointList.push_back(pt);
        pointToFaceInds.push_back(emptyList);
        ptind=pointList.size()-1;
        pointIntMap[pt]=ptind;
      } else ptind=pointIntMap[pt];
//      printf("%d ",ptind);
      polygon.push_back(ptind);
      pointToFaceInds[ptind].push_back(i);
    }
//    printf("\n");
    polygons.push_back(polygon);
  }

}

int operator==(const CutFace &a, const CutFace &b)
{
        if(a.a != b.a) return 0;
        if(a.b != b.b) return 0;
        if(a.c != b.c) return 0;
        if(a.d != b.d) return 0;
        return 1;
}

unsigned int hash_value(const CutFace& r) {
	double x=r.a+10*r.b+100*r.c+1000*r.d;
        unsigned int i;
	i=*((int *) &x);
        return i;
}

std::vector<CutFace> calculateEdgeFaces( std::vector<Vector3d> &pointList,std::vector<intList> &polygons, std::vector<intList>  &pointToFaceInds, std::vector<CutFace> &normfaces)
{
  std::vector<CutFace> edgeFaces;
  std::unordered_set<CutFace, boost::hash<CutFace> > edgeFacePresent;
  for(int i=0;i<polygons.size();i++)
  { 
    intList &poly = polygons[i];
    int n=poly.size();
    if(n < 3) continue;
    // normalvektor
    Vector3d p1, p2, p3;
    p1=pointList[poly[0]];
    p2=pointList[poly[1]];
    p3=pointList[poly[2]];
    Vector3d nb=(p2-p1).cross(p3-p1).normalized();
    CutFace cf;
    cf.a=nb[0];
    cf.b=nb[1];
    cf.c=nb[2];
    cf.d=-(cf.a*p1[0]+cf.b*p1[1]+cf.c*p1[2]);
    normfaces.push_back(cf);
//    printf("nb %.2g/%.2g/%.2g\n",nb[0],nb[1],nb[2]);
    for(int j=0;j<n;j++)
    {
      // find adajacent face
      int ind1=poly[j];
      int ind2=poly[(j+1)%n];
      int faceindfound=-1;
      for(int k=0;k<pointToFaceInds[ind1].size();k++) {
        int faceind=pointToFaceInds[ind1][k];
	if(faceind == i) continue;
	for(int l=0;l<polygons[faceind].size();l++) {
	  if(polygons[faceind][l] == ind2) faceindfound=faceind;
	}
      }
      if(faceindfound == -1) continue;
      intList &opoly = polygons[faceindfound];
      p1=pointList[opoly[0]];
      p2=pointList[opoly[1]];
      p3=pointList[opoly[2]];
      Vector3d no=(p2-p1).cross(p3-p1).normalized();
      
      // create edge face
      p1=pointList[ind2]-pointList[ind1]; // this is safe against coplanar  adjacent faces
      p2=no+nb;
      p3=p2.cross(p1).normalized();

      p1=pointList[ind1];
      cf.a=p3[0];
      cf.b=p3[1];
      cf.c=p3[2];
      cf.d=-(cf.a*p1[0]+cf.b*p1[1]+cf.c*p1[2]);
      int swap=0;
      if(cf.a < 0) swap=1;
      if(cf.a == 0) {
 	if(cf.b < 0) swap=1;
 	if(cf.b == 0) {
           if(cf.c < 0) swap=1;
 	}
     }
     if(swap) { cf.a =-cf.a; cf.b =-cf.b; cf.c =-cf.c; cf.d =-cf.d; }
//      printf("nf\t%.2g\t%.2g\t%.2g\t%.2g\n",cf.a, cf.b, cf.c, cf.d);
      if(!edgeFacePresent.count(cf)) { 
      	edgeFaces.push_back(cf);
	edgeFacePresent.insert(cf);
      } 
    }
  }
  return edgeFaces;
}
struct ProgramState
{
	intList validFaces;
	int state=0;
	int resultind;
};

std::vector<ProgramState> programStack;


int generateProgram(intList &table, std::vector<CutProgram> &program,std::vector<CutFace> &edgeFaces, const std::vector<intList> &faces, intList &validFaces) 
{
	std::vector<int> posFaces, negFaces;
	int i,j,v;
	CutProgram cp;
	// find out , which row has most equal balance between + and -
	int rate,ratebest=-1,edgebest=-1;
	int edgeFaceLen = edgeFaces.size();
	int validFacesLen = validFaces.size();
	int facesLen=faces.size();
//	printf("generateProgram round=%d\n",generateRound++);
	for(i=0;i<edgeFaceLen;i++) {
		int poscount=0;
		int negcount=0;
		for(j=0;j<validFacesLen;j++)
		{
			v=table[i*facesLen+validFaces[j]];

			if(v == 1) poscount++;
			if(v == -1) negcount++;
		}
		rate=poscount<negcount?poscount:negcount;
		if(rate > ratebest) {
			ratebest=rate;
			edgebest=i;
		}

	}
	if(edgebest == -1) {
		printf("Program Error!\n");
		exit(1);
	}
	cp.a=edgeFaces[edgebest].a;
	cp.b=edgeFaces[edgebest].b;
	cp.c=edgeFaces[edgebest].c;
	cp.d=edgeFaces[edgebest].d;

	// split into positive and negative branch
	for(int i=0;i<validFaces.size();i++)
	{
		switch(table[edgebest*facesLen+validFaces[i]])
		{
			case 1:
				posFaces.push_back(validFaces[i]);
				break;
			case 0:
				posFaces.push_back(validFaces[i]);
				negFaces.push_back(validFaces[i]);
				break;
			case -1:
				negFaces.push_back(validFaces[i]);
				break;
		}
	}

	int startind=program.size();
	program.push_back(cp);

	if(posFaces.size() == validFaces.size())
	{
		for(i=0;i<edgeFaces.size();i++)
		{
			for(j=0;j< validFaces.size();j++) 
			{
				switch(table[i*facesLen+validFaces[j]])
				{
					case 1:printf("+"); break;
					case 0:printf("/"); break;
					case -1:printf("/"); break;
				}
			}
			printf("\n");
		}
		printf("faces are \n");
		for(i=0;i<validFaces.size();i++) {
			int faceind=validFaces[i];
			for(j=0;j<faces[faceind].size();j++)
			{
				printf("%d ",faces[faceind][j]);
			}
			printf("\n");
		}
		exit(1);

		program[startind].posbranch = ~(posFaces[0]);
		program[startind].negbranch = ~(posFaces[1]);
		return startind;
	}

	if(negFaces.size() == validFaces.size())
	{
		program[startind].posbranch = ~(negFaces[0]);
		program[startind].negbranch = ~(negFaces[1]);
		return startind;
	}


	if(negFaces.size() > 1) {
  		ProgramState state;
		state.validFaces=negFaces;	
		state.resultind=~startind;
		programStack.push_back(state);
	} else {
		program[startind].negbranch = ~(negFaces[0]);
	}

	if(posFaces.size() > 1) {
  		ProgramState state;
		state.validFaces=posFaces;
		state.resultind=startind;
		programStack.push_back(state);
	} else {
		program[startind].posbranch = ~(posFaces[0]);
	}
	return startind;
}

int generateProgramFlat(intList &table, std::vector<CutProgram> &program, std::vector<CutFace> &edgeFaces, const std::vector<intList> &faces, std::vector<ProgramState> &stack) 
{
	printf("flat\n");
	while(1)
	{
		if(stack.size() == 0) return 0;
		ProgramState state = stack[stack.size()-1];
		stack.pop_back();

		int result=generateProgram(table ,program, edgeFaces, faces,state.validFaces); // create recursive program
		if(state.resultind == 0x80000000) continue;
		if(state.resultind >= 0) program[state.resultind].posbranch = result;		
		else program[~(state.resultind)].negbranch = result;

	}
	return 0;
}

double evaluateProgram(std::vector<CutProgram> &program,int ind,std::vector<CutFace> &normFaces, double x,double y, double z)
{
	double e;
	int nextind;
	while(1) {
		CutProgram &prg = program[ind];
		e=prg.a*x+prg.b*y+prg.c*z+prg.d;
		if(e >= 0) nextind=prg.posbranch; else nextind=prg.negbranch;
		if(nextind < 0) {
			CutFace cf = normFaces[~nextind];
			double d=cf.a*x+cf.b*y+cf.c*z+cf.d;
			return d;
		}
		ind=nextind;
	}

	return 0;
}



// Libfive Oracle interface
OpenSCADOracle::OpenSCADOracle( const std::vector<CutProgram> &program, const std::vector<CutFace> &normFaces):program(program), normFaces(normFaces)
{
        // Nothing to do here
}

void OpenSCADOracle::evalInterval(libfive::Interval& out) {
	// Just pick a big ambiguous value.
	out = {-10000.0, 10000.0};
}

int evalCalled=0;
void OpenSCADOracle::evalPoint(float& out, size_t index) {
        const auto pt = points.col(index);
	evalCalled++;
        out = evaluateProgram(this->program,0,this->normFaces, pt.x(), pt.y(), pt.z());
}

void OpenSCADOracle::checkAmbiguous( Eigen::Block<Eigen::Array<bool, 1, LIBFIVE_EVAL_ARRAY_SIZE>, 1, Eigen::Dynamic> /* out */)
{
}

void OpenSCADOracle::evalFeatures(boost::container::small_vector<libfive::Feature, 4>& out) {
        const float EPSILON = 1e-6;
        float center, dx, dy, dz;

        Eigen::Vector3f before = points.col(0);
        evalPoint(center);

        points.col(0) = before + Eigen::Vector3f(EPSILON, 0.0, 0.0);
        evalPoint(dx);

        points.col(0) = before + Eigen::Vector3f(0.0, EPSILON, 0.0);
        evalPoint(dy);

        points.col(0) = before + Eigen::Vector3f(0.0, 0.0, EPSILON);
        evalPoint(dz);

        points.col(0) = before;

        out.push_back(Eigen::Vector3f(
            (dx - center) / EPSILON,
            (dy - center) / EPSILON,
            (dz - center) / EPSILON));
}

#ifdef ENABLE_PYTHON
PyObject *ifrep(const PolySet *ps)
{
  printf("ifrep\n");
  std::vector<Vector3d> pointList; // list of all the points in the object
  std::vector<intList> polygons; // list polygons represented by indexes
  std::vector<intList>  pointToFaceInds; //  mapping pt_ind -> list of polygon inds which use it

  convertToIndex(ps,pointList, polygons,pointToFaceInds); // index umwandeln
  printf("%d Faces, %d Points\n",polygons.size(),pointList.size());

  std::vector<CutFace> edgeFaces;
  std::vector<CutFace> normFaces;
  edgeFaces = calculateEdgeFaces(pointList, polygons,pointToFaceInds,normFaces);
  printf("%d EdgeFaces generated\n",edgeFaces.size());

  std::vector<int> table; // x(0) dimenstion faces y(1) dimenions edgefas
  for(int i=0;i<edgeFaces.size();i++) // create table
  {
    CutFace &ef = edgeFaces[i];
    for(int j=0;j<polygons.size();j++)
    {
      intList &poly=polygons[j];
      int poscount=0, negcount=0;
      for(int k=0;k<poly.size(); k++)
      {
	      Vector3d pt=pointList[poly[k]];
	      double e=ef.a*pt[0]+ef.b*pt[1]+ef.c*pt[2]+ef.d;
	      if(e >  0.00001) poscount++;
	      if(e < -0.00001) negcount++;
      }      
      if(poscount > 0 && negcount == 0) table.push_back(1);
      else if(poscount == 0 && negcount > 0) table.push_back(-1);
      else table.push_back(0); 
    }	    
  }	  
  printf("Table generated\n");


  ProgramState state;
  for(int i=0;i<polygons.size();i++) state.validFaces.push_back(i); 
  state.state=0;
  state.resultind=0x80000000;
  programStack.push_back(state); // initially all the work
  std::vector<CutProgram> program;
  int startind=generateProgramFlat(table ,program,edgeFaces, polygons,programStack); // create recursive program
  for(int i=0;i<program.size();i++) {
	printf("%d\t%.3f\t%.3f\t%.3f\t%.3f\tP:%d\tN:%d\n",i,program[i].a,program[i].b,program[i].c,program[i].d,program[i].posbranch, program[i].negbranch);
  }
  /*
  printf("dist=%f\n",evaluateProgram(program,startind,normFaces, 0.5,0.5,1.5));
  printf("dist=%f\n",evaluateProgram(program,startind,normFaces, 0.5,0.5,-0.5));
  printf("dist=%f\n",evaluateProgram(program,startind,normFaces, 1.5,0.5,0.5));
  printf("dist=%f\n",evaluateProgram(program,startind,normFaces, -0.5,0.5,0.5));
  printf("dist=%f\n",evaluateProgram(program,startind,normFaces, 0.5,1.5,0.5));
  printf("dist=%f\n",evaluateProgram(program,startind,normFaces, 0.5,-0.5,0.5));
  printf("dist=%f\n",evaluateProgram(program,startind,normFaces, 0.5,0.5,0.9));
*/ 
  std::vector<libfive::Tree*> oc;
  Tree t=libfive::Tree(std::unique_ptr<OracleClause>(new OpenSCADOracleClause(program, normFaces)));
  oc.push_back(new Tree(t));
  printf("eval Called is %d\n",evalCalled);
  evalCalled=0;
  return PyLibFiveObjectFromTree(&PyLibFiveType,oc);		  
}
#endif

