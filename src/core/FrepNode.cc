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



#include <cmath>
#include <sstream>

#include "libfive/render/brep/dc/dc_mesher.hpp"
#include "libfive/render/brep/dc/dc_worker_pool.hpp"
#include "libfive/render/brep/region.hpp"
#include "libfive/render/brep/mesh.hpp"

#include <hash.h>
#include <unordered_set>


using namespace libfive;
#define OPT_META	1
typedef struct
{
	Vector3d pos;
	Vector3d norm;
	int opt;
} SDFVertex;

typedef struct 
{
	int i[3];
} SDFTriangle ;

typedef struct {
	int i[2];
}  SDFTwoInd;

unsigned int hash_value(const SDFTwoInd& r) {
        unsigned int i;
        i=r.i[0] |(r.i[1]<<16);
        return i;
}

int operator==(const SDFTwoInd &e1, const SDFTwoInd &e2) 
{
        if(e1.i[0] == e2.i[0] && e1.i[1] == e2.i[1]) return 1;
        return 0;
}

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
	printf("align pt :%g/%g/%g norm:%g/%g/%g\n",vert.pos[0],vert.pos[1],vert.pos[2], vert.norm[0],vert.norm[1],vert.norm[2]);
	if(vert.norm.norm() < 1e-9){
		vert.norm=SDF_calculateNormComp(tr,vert.pos,Vector3d(0.01,0,0));
		vert.norm.normalize();
	}
	printf("start loop\n");
	double sdf = sdf_func(tr,vert.pos);
	int fails=0;
	do
	{
		// now move the pt
		Vector3d pt_bak=vert.pos;
		vert.pos -= sdf * vert.norm;
		printf("pt is %g/%g/%g\n",vert.pos[0],vert.pos[1],vert.pos[2]);
		double sdftest = sdf_func(tr,vert.pos);
		printf("sdftest is %g\n",sdftest);
		if(sdftest > 10) exit(1);
		if(isinf(sdftest)) exit(1);
		double b=(sdf - sdftest)/sdf;
		printf("b=%g\n",b);
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
	printf("align done\n");
	return 0;
}

void split_metaloops(libfive::Tree &tr, std::vector<SDFVertex> &vert, std::vector<SDFTriangle> &triangles) {
	// Now find META looops
	double sep=0.25; // TODO sep needs  to be bigger than 0.01
	std::unordered_map<int, SDFTwoInd  > meta_piece;
	SDFTwoInd piece;
	int ind1, ind2;
	// store META loops in hash
	for(int i=0;i<triangles.size();i++)
	{
		for(int j=0;j<3;j++) {
			ind1=triangles[i].i[j]; // TODO METAS cannot get finished
			ind2=triangles[i].i[(j+1)%3];
			if((vert[ind1].opt & OPT_META) && vert[ind2].opt & OPT_META) {
//				printf("META %d->%d\n",ind1, ind2);
				if(meta_piece.count(ind1) == 0) {
					piece.i[0]=ind2;
					piece.i[1]=-1;
					meta_piece[ind1]=piece;
				} else {
					meta_piece[ind1].i[1]=ind2;
				}
			}
		}
	}		
	do
	{
		//  build chains
		//  find next chain ind
		int  ind=-1;
		for(auto kv: meta_piece) {
			if(kv.second.i[0] != -1){  ind=kv.second.i[0]; break; }
			if(kv.second.i[1] != -1){  ind=kv.second.i[1]; break; }
		}
		if(ind == -1) break;

		std::vector<int> chain;
		int newind;
		int closed=0;
		do
		{
			if(chain.size() > 0 && ind == chain[0]){
				closed=1;
				break;
			}


			chain.push_back(ind);
			newind=-1;
			for(int i=0;newind == -1 && i<2;i++)
			{
				newind=meta_piece[ind].i[i];
				if(chain.size() >= 2 && chain[chain.size()-2] ==  newind) newind=-1;
				if(newind != -1)  {
					meta_piece[ind].i[i]=-1; 
				}
			}
			if(newind == -1) break;
			// also disable reverse:
			if(meta_piece[newind].i[0] == ind) meta_piece[newind].i[0]=-1;
			if(meta_piece[newind].i[1] == ind) meta_piece[newind].i[1]=-1;
			ind=newind;
		} while(1);
		if(!closed) {
			continue; // notr usable
		} 

		printf("Chain is "); 
		for(int i=0;i<chain.size();i++)
			printf("%d ",chain[i]);
		printf("\n");
		
		std::vector<int> chain_mirror;
		std::vector<Vector3d> chain_norm;
		int n = chain.size();
		// create norm vectors
		for(int i=0;i<n;i++) {
			Vector3d p1, p2, p3, nrm;
			p1=vert[chain[(i+n-1)%n]].pos;
			p2=vert[chain[i%n]].pos;
			p3=vert[chain[(i+n+1)%n]].pos;
			nrm=(p2-p1).cross(p3-p2);
			chain_norm.push_back(nrm);
		}
		// duplicate points
		for(int i=0;i<chain.size();i++) {
			 int pos=i;
			 Vector3d sepdir;
			 do {
				 sepdir=chain_norm[pos%n];
				 pos++;
			 }
			 while(sepdir.norm() < 0.1);
			 sepdir.normalize();
			 SDFVertex vert_dup=vert[chain[i]];
			 chain_mirror.push_back(vert.size());
			 vert_dup.pos += sepdir * sep;
			 vert.push_back(vert_dup);
			 vert[chain[i]].pos -= sepdir * sep; 
		}
		// map points
		//  TODO livbfive equation anzapfgen
		//  TODO eigener tree ?
		//  TODO golden ratio
		//  TODO chains nicht doppeln
		//  TODO torus probieren
		SDFTriangle tri;
		for(int i=0;i<triangles.size();i++)
		{
			Vector3d cent(0,0,0);
			int meta_ind=-1;
			for(int j=0;j<3;j++) {
				ind=triangles[i].i[j]; 
				cent = cent + vert[ind].pos;
				if((vert[ind].opt & OPT_META)) meta_ind=ind;
			}
			cent=cent /3.0;
			if(meta_ind != -1) {
				std::vector<int>::iterator it;
				it=std::find(chain.begin(),chain.end(),meta_ind);
				if(it != chain.end()) {
					int pos=it-chain.begin();
					Vector3d p1,p2,p3,nrm;
					do
					{
						nrm=chain_norm[pos%n];
						pos++;
					}
					while(nrm.norm() < 0.1);
					nrm.normalize();
//					printf("n=%g/%g/%g\n",nrm[0],nrm[1],nrm[2]);
					double dist=(cent-p2).dot(nrm);
//					printf("dist=%g\n",dist);
					if(dist > 0) { 
						for(int j=0;j<3;j++) {
							ind=triangles[i].i[j]; // TODO METAS cannot get finished
							it=std::find(chain.begin(),chain.end(),ind);
							if(it != chain.end()) {
								int pos=it-chain.begin();
//								printf("repl pos is %d\n",pos);
								triangles[i].i[j]=chain_mirror[pos];
							}

						}

					}

				}
			
				// if tri has meta point,calculatenormal  of meta plane
			}
		}		
		// redo norm vector for chain inds
		//
		// go through all triangles and calculate their mid point
		for(int i=0;i<chain.size();i++) {
			Vector3d diff1(0.01,0,0);
			double sdf;
			int ind;

			ind=chain[i];
			vert[ind].norm =SDF_calculateNormComp(tr,vert[ind].pos, diff1);
		        sdf 	= sdf_func(tr, vert[ind].pos);
			vert[ind].pos -= vert[ind].norm*sdf;

			ind=chain_mirror[i];
			vert[ind].norm =SDF_calculateNormComp(tr,vert[ind].pos, diff1);
		        sdf 	= sdf_func(tr, vert[ind].pos);
			vert[ind].pos -= vert[ind].norm*sdf;
		}
		// then create filling planes
		for(int i=0;i<n-2;i++) {
			tri.i[0]=chain[0]; // TODO better alg 
			tri.i[1]=chain[i+2];
			tri.i[2]=chain[i+1];
			triangles.push_back(tri);

			tri.i[0]=chain_mirror[0]; 
			tri.i[1]=chain_mirror[i+1];
			tri.i[2]=chain_mirror[i+2];
			triangles.push_back(tri);
		}

		for(int i=0;i<n;i++) // remove the meta opt
		{
			vert[chain[i]].opt=0;
			vert[chain_mirror[i]].opt=0;
		}
	}
	while(1);
}

PolySet *MySDF(libfive::Tree &tr,Vector3d pmin, Vector3d pmax,double tol)
{
	std::vector<SDFVertex> vert;
	SDFVertex v;
	std::vector<SDFTriangle> tris_work;
	std::vector<SDFTriangle> tris_finished;
	SDFTriangle tri;

	// form cube
	v.opt = 0;
	v.norm=Vector3d(0,0,0);
	v.pos = Vector3d(pmin[0],pmin[1],pmin[2]); vert.push_back(v);
	v.pos = Vector3d(pmax[0],pmin[1],pmin[2]); vert.push_back(v); 
	v.pos = Vector3d(pmax[0],pmax[1],pmin[2]); vert.push_back(v); 
	v.pos = Vector3d(pmin[0],pmax[1],pmin[2]); vert.push_back(v); 
	v.pos = Vector3d(pmin[0],pmin[1],pmax[2]); vert.push_back(v); 
	v.pos = Vector3d(pmax[0],pmin[1],pmax[2]); vert.push_back(v); 
	v.pos = Vector3d(pmax[0],pmax[1],pmax[2]); vert.push_back(v); 
	v.pos = Vector3d(pmin[0],pmax[1],pmax[2]); vert.push_back(v); 

	tri.i[0]=1; tri.i[1]=5; tri.i[2]=0; tris_work.push_back(tri);
	tri.i[0]=0; tri.i[1]=5; tri.i[2]=4; tris_work.push_back(tri);

	tri.i[0]=2; tri.i[1]=5; tri.i[2]=1; tris_work.push_back(tri);
	tri.i[0]=6; tri.i[1]=5; tri.i[2]=2; tris_work.push_back(tri);

	tri.i[0]=4; tri.i[1]=5; tri.i[2]=7; tris_work.push_back(tri);
	tri.i[0]=7; tri.i[1]=5; tri.i[2]=6; tris_work.push_back(tri);

	tri.i[0]=0; tri.i[1]=3; tri.i[2]=1; tris_work.push_back(tri);
	tri.i[0]=1; tri.i[1]=3; tri.i[2]=2; tris_work.push_back(tri);

	tri.i[0]=4; tri.i[1]=3; tri.i[2]=0; tris_work.push_back(tri);
	tri.i[0]=7; tri.i[1]=3; tri.i[2]=4; tris_work.push_back(tri);

	tri.i[0]=2; tri.i[1]=3; tri.i[2]=6; tris_work.push_back(tri);
	tri.i[0]=6; tri.i[1]=3; tri.i[2]=7; tris_work.push_back(tri);

	// hier SDF
	// alle vertices anpassen
	int count=0;
	for(int i=0;i<vert.size();i++) {
		SDF_align(tr,vert[i] ,tol);
	}
	printf("start normal splitting\n");
	int round=0; // TODO weg
	while(tris_work.size() > 0) {
		std::vector<SDFTriangle> tris_new;
		std::unordered_map<SDFTwoInd, int,boost::hash<SDFTwoInd> > edges;
		printf("Round %d tris_work is %d\n",round,tris_work.size());

		for(int i=0;i<tris_work.size();i++) {
			tri=tris_work[i];
			Vector3d p1, p2;
			SDFVertex pmid;
			pmid.opt=0;
			double dist;
			SDFTwoInd e;
			int ind1,ind2;
			// jede kante  preufen und  schauen ob sie gesplittetwerden muss, dann neuen index ausrechnen
			for(int j=0;j<3;j++) {
				ind1=tri.i[j];
				ind2=tri.i[(j+1)%3];
				e.i[0]=ind1<ind2?ind1:ind2;
				e.i[1]=ind1>ind2?ind1:ind2;
				if(edges.count(e) == 0) {
					p1=vert[ind1].pos;
					p2=vert[ind2].pos;
					dist=(p2-p1).norm();
					gboolean split=true;
					if(dist < 0.3) split=false;
				        if(count >1000 ) split=false;
					if(vert[ind1].opt & OPT_META) split=false;
					if(vert[ind2].opt & OPT_META) split=false;
					if(round >1 ) split=false; // TODO weg // TODO parameter
					if(split){
						printf("Split %d/%d\n",i,j);
						double ratio=0.5; // 0.618; // golden ratio // TODO != 0.5 wird sehr unschoen
						if(round&1) ratio=1-ratio;								   
						pmid.pos=p1*ratio+p2*(1-ratio);
						pmid.opt=0;
						printf("norm from %g/%g/%g and %g/%g/%g\n",vert[ind1].norm[0],vert[ind1].norm[1],vert[ind1].norm[2],vert[ind2].norm[0],vert[ind2].norm[1],vert[ind2].norm[2]);
						pmid.norm =vert[ind1].norm*ratio+vert[ind2].norm*(1-ratio);
						pmid.norm.normalize();
						printf("start align\n");
						if(SDF_align(tr,pmid,tol))
						{
							pmid.pos=p1*ratio+p2*(1-ratio);
							pmid.opt=OPT_META;
						}
						printf("end align\n");
						
						edges[e]=vert.size(); // new index
						vert.push_back(pmid);

					}
					count++;

				}
			}
		}
		// dann jedes dreick tatsaechlich splitten
		for(int i=0;i<tris_work.size();i++) {
			tri=tris_work[i];
			int si[3];
			int ind1, ind2;
			SDFTwoInd e;
			for(int j=0;j<3;j++) {
				ind1=tri.i[j];
				ind2=tri.i[(j+1)%3];
				e.i[0]=ind1<ind2?ind1:ind2;
				e.i[1]=ind1>ind2?ind1:ind2;
				if(edges.count(e) == 0) si[j]=-1;
				else si[j]=edges[e];
			}
			SDFTriangle tri_new; 
			if(si[2] == -1 && si[1] == -1 && si[0] == -1) {
				tris_finished.push_back(tri);

			} else if(si[2] == -1 && si[1] == -1 && si[0] != -1) {
				tri_new.i[0]=tri.i[0]; tri_new.i[1]=si[0]; tri_new.i[2]=tri.i[2]; tris_new.push_back(tri_new);
				tri_new.i[0]=tri.i[2]; tri_new.i[1]=si[0]; tri_new.i[2]=tri.i[1]; tris_new.push_back(tri_new);
			} else if(si[2] == -1 && si[1] != -1 && si[0] == -1) {
				tri_new.i[0]=tri.i[1]; tri_new.i[1]=si[1]; tri_new.i[2]=tri.i[0]; tris_new.push_back(tri_new);
				tri_new.i[0]=tri.i[0]; tri_new.i[1]=si[1]; tri_new.i[2]=tri.i[2]; tris_new.push_back(tri_new);
			} else if(si[2] != -1 && si[1] == -1 && si[0] == -1) {
				tri_new.i[0]=tri.i[2]; tri_new.i[1]=si[2]; tri_new.i[2]=tri.i[1]; tris_new.push_back(tri_new);
				tri_new.i[0]=tri.i[1]; tri_new.i[1]=si[2]; tri_new.i[2]=tri.i[0]; tris_new.push_back(tri_new);
			
			} else if(si[2] == -1 && si[1] != -1 && si[0] != -1) {
				tri_new.i[0]=tri.i[0]; tri_new.i[1]=   si[0]; tri_new.i[2]=tri.i[2]; tris_new.push_back(tri_new);
				tri_new.i[0]=tri.i[2]; tri_new.i[1]=   si[0]; tri_new.i[2]=   si[1]; tris_new.push_back(tri_new);
				tri_new.i[0]=   si[0]; tri_new.i[1]=tri.i[1]; tri_new.i[2]=   si[1]; tris_new.push_back(tri_new);
			} else if(si[2] != -1 && si[1] != -1 && si[0] == -1) {
				tri_new.i[0]=tri.i[1]; tri_new.i[1]=   si[1]; tri_new.i[2]=tri.i[0]; tris_new.push_back(tri_new);
				tri_new.i[0]=tri.i[0]; tri_new.i[1]=   si[1]; tri_new.i[2]=   si[2]; tris_new.push_back(tri_new);
				tri_new.i[0]=   si[1]; tri_new.i[1]=tri.i[2]; tri_new.i[2]=   si[2]; tris_new.push_back(tri_new);
			} else if(si[2] != -1 && si[1] == -1 && si[0] != -1) {
				tri_new.i[0]=tri.i[2]; tri_new.i[1]=   si[2]; tri_new.i[2]=tri.i[1]; tris_new.push_back(tri_new);
				tri_new.i[0]=tri.i[1]; tri_new.i[1]=   si[2]; tri_new.i[2]=   si[0]; tris_new.push_back(tri_new);
				tri_new.i[0]=   si[2]; tri_new.i[1]=tri.i[0]; tri_new.i[2]=   si[0]; tris_new.push_back(tri_new);
			} else if(si[2] != -1 && si[1] != -1 && si[0] != -1) {
				tri_new.i[0]=tri.i[0]; tri_new.i[1]=si[0]; tri_new.i[2]=si[2]; tris_new.push_back(tri_new);
				tri_new.i[0]=tri.i[1]; tri_new.i[1]=si[1]; tri_new.i[2]=si[0]; tris_new.push_back(tri_new);
				tri_new.i[0]=tri.i[2]; tri_new.i[1]=si[2]; tri_new.i[2]=si[1]; tris_new.push_back(tri_new);
				tri_new.i[0]=si[0]; tri_new.i[1]=si[1]; tri_new.i[2]=si[2]; tris_new.push_back(tri_new);
			} else {
				printf("dont  know how to split triangle\n");
				exit(1);
			}
	
		}
		split_metaloops(tr,vert, tris_new);
		tris_work = tris_new;
		round++;
	}
	//
	auto p = new PolySet(3, true);
	printf("%d Points and %d Triangles generated\n",vert.size(),tris_finished.size());
	for(int i=0;i<tris_finished.size();i++) {
		p->append_poly(3);
		for(int j=0;j<3;j++) {
			int ind=tris_finished[i].i[j];
			p->append_vertex(vert[ind].pos[0],vert[ind].pos[1],vert[ind].pos[2]);
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
		printf("render end %d\n",mesh->branes.size());
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
		printf("convert end\n");
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

