#pragma once

#include "Geometry.h"
#include "linalg.h"
#include "GeometryUtils.h"
#include "Polygon2d.h"
#include "boost-utils.h"

#include <vector>
#include <string>
#include <unordered_map>
#include <hash.h>

int operator==(const Vector3d &a, const Vector3d &b);

class PolySet : public Geometry
{
public:
  VISITABLE_GEOMETRY();
  PolygonsInd polygons_ind;
  std::vector<Vector3d> points;
  std::unordered_map<Vector3d, int> pointMap;

  PolySet(unsigned int dim, boost::tribool convex = unknown);
  PolySet(Polygon2d origin);
  int pointIndex(const Vector3d &pt);

  const Polygon2d& getPolygon() const { return polygon; }

  size_t memsize() const override;
  BoundingBox getBoundingBox() const override;
  std::string dump() const override;
  unsigned int getDimension() const override { return this->dim; }
  bool isEmpty() const override { return polygons_ind.size() == 0; }
  Geometry *copy() const override { return new PolySet(*this); }

  void quantizeVertices(std::vector<Vector3d> *pPointsOut = nullptr);
  size_t numFacets() const override { return polygons_ind.size(); }
  void reserve(size_t numFacets) { polygons_ind.reserve(numFacets); }
  void append_coord(const Vector3d &coord);
  void append_poly(size_t expected_vertex_count);
  void append_poly(const Polygon& poly); // DEPRECATED
  void append_poly(const IndexedFace& poly);

  void append_vertex(double x, double y, double z = 0.0); // DEPRECATED
  void append_vertex(const Vector3d& v); // DEPRECATED
  void append_vertex(const Vector3f& v); // DEPRECATED
  void append_vertex(int ind);

  void insert_vertex(double x, double y, double z = 0.0); // DEPRECATED
  void insert_vertex(const Vector3d& v); // DEPRECATED
  void insert_vertex(const Vector3f& v); // DEPRECATED
  void insert_vertex(int ind); 
  void append(const PolySet& ps);

  void transform(const Transform3d& mat) override;
  void resize(const Vector3d& newsize, const Eigen::Matrix<bool, 3, 1>& autosize) override;

  bool is_convex() const;
  boost::tribool convexValue() const { return this->convex; }

private:
  Polygon2d polygon;
  unsigned int dim;
  mutable boost::tribool convex;
  mutable BoundingBox bbox;
  mutable bool dirty;
};
