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

#include "RotateExtrudeNode.h"
#include "module.h"
#include "ModuleInstantiation.h"
#include "Children.h"
#include "Parameters.h"
#include "printutils.h"
#include "iofileutils.h"
#include "Builtins.h"
#include "handle_dep.h"
#include <cmath>
#include <sstream>
#include <boost/assign/std/vector.hpp>
using namespace boost::assign; // bring 'operator+=()' into scope

#include <boost/filesystem.hpp>
#include <Python.h>
#include "pyopenscad.h"

namespace fs = boost::filesystem;

static std::shared_ptr<AbstractNode> builtin_rotate_extrude(const ModuleInstantiation *inst, Arguments arguments, const Children& children)
{
  auto node = std::make_shared<RotateExtrudeNode>(inst);

  Parameters parameters = Parameters::parse(std::move(arguments), inst->location(),
                                            {"file", "layer", "origin", "scale"},
                                            {"convexity", "angle"}
                                            );

  node->fn = parameters["$fn"].toDouble();
  node->fs = parameters["$fs"].toDouble();
  node->fa = parameters["$fa"].toDouble();

  if (!parameters["file"].isUndefined()) {
    LOG(message_group::Deprecated, Location::NONE, "", "Support for reading files in rotate_extrude will be removed in future releases. Use a child import() instead.");
    std::string  filename = lookup_file(parameters["file"].toString(), inst->location().filePath().parent_path().string(), parameters.documentRoot());
    node->filename = filename;
    handle_dep(filename);
  }

  node->layername = parameters["layer"].isUndefined() ? "" : parameters["layer"].toString();
  node->convexity = static_cast<int>(parameters["convexity"].toDouble());
  bool originOk = parameters["origin"].getVec2(node->origin_x, node->origin_y);
  originOk &= std::isfinite(node->origin_x) && std::isfinite(node->origin_y);
  if (parameters["origin"].isDefined() && !originOk) {
    LOG(message_group::Warning, inst->location(), parameters.documentRoot(), "rotate_extrude(..., origin=%1$s) could not be converted", parameters["origin"].toEchoStringNoThrow());
  }
  node->scale = parameters["scale"].toDouble();
  node->angle = 360;
  parameters["angle"].getFiniteDouble(node->angle);

  if (node->convexity <= 0) node->convexity = 2;

  if (node->scale <= 0) node->scale = 1;

  if ((node->angle <= -360) || (node->angle > 360)) node->angle = 360;

  if (node->filename.empty()) {
    children.instantiate(node);
  } else if (!children.empty()) {
    LOG(message_group::Warning, inst->location(), parameters.documentRoot(),
        "module %1$s() does not support child modules when importing a file", inst->name());
  }


  return node;
}

PyObject* python_rotate_extrude(PyObject *self, PyObject *args, PyObject *kwargs)
{
  std::shared_ptr<AbstractNode> child;

  auto node = std::make_shared<RotateExtrudeNode>(&todo_fix_inst);

  PyObject *obj = NULL;

  char *layer=NULL;
  int convexity=1;
  double scale=1.0;
  double angle=360.0;
  PyObject *origin=NULL;


  char * kwlist[] ={"obj","layer","convexity","scale",NULL};

   if (!PyArg_ParseTupleAndKeywords(args, kwargs, "O!|siddO!", kwlist, 
                          &PyOpenSCADType,
                          &obj,
			  &layer,
			  &convexity,
			  &scale,
			  &angle,
			  &PyList_Type,
			  &origin
                          ))
        return NULL;

  child = PyOpenSCADObjectToNode(obj);

  node->fn=10;
  node->fs=10;
  node->fa=10;

  if(layer != NULL) node->layername = layer;
  node->convexity = convexity;
  node->scale = scale;
  node->angle = angle;

  if(origin != NULL && PyList_Check(origin) && PyList_Size(origin) == 2) {
	  node->origin_x=PyFloat_AsDouble(PyList_GetItem(origin, 0));
	  node->origin_y=PyFloat_AsDouble(PyList_GetItem(origin, 1));
  }



  if (node->convexity <= 0) node->convexity = 2;
  if (node->scale <= 0) node->scale = 1;
  if ((node->angle <= -360) || (node->angle > 360)) node->angle = 360;

  node->children.push_back(child);
  return PyOpenSCADObjectFromNode(&PyOpenSCADType,node);
}

PyObject* python_rotate_extrude_oo(PyObject *self, PyObject *args, PyObject *kwargs)
{
	PyObject *new_args=python_oo_args(self,args);
	PyObject *result = python_rotate_extrude(self,new_args,kwargs);
//	Py_DECREF(&new_args);
	return result;
}


std::string RotateExtrudeNode::toString() const
{
  std::ostringstream stream;

  stream << this->name() << "(";
  if (!this->filename.empty()) { // Ignore deprecated parameters if empty
    fs::path path((std::string)this->filename);
    stream <<
      "file = " << this->filename << ", "
      "layer = " << QuotedString(this->layername) << ", "
      "origin = [" << std::dec << this->origin_x << ", " << this->origin_y << "], "
      "scale = " << this->scale << ", "
           << "timestamp = " << (fs::exists(path) ? fs::last_write_time(path) : 0) << ", "
    ;
  }
  stream <<
    "angle = " << this->angle << ", "
    "convexity = " << this->convexity << ", "
    "$fn = " << this->fn << ", $fa = " << this->fa << ", $fs = " << this->fs << ")";

  return stream.str();
}

void register_builtin_dxf_rotate_extrude()
{
  Builtins::init("dxf_rotate_extrude", new BuiltinModule(builtin_rotate_extrude));

  Builtins::init("rotate_extrude", new BuiltinModule(builtin_rotate_extrude),
  {
    "rotate_extrude(angle = 360, convexity = 2)",
  });
}
