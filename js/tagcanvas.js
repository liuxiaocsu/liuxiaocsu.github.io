/**
 * Copyright (C) 2010-2015 Graham Breach
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
/**
 * TagCanvas 2.9
 * For more information, please contact <graham@goat1000.com>
 */
(function(){
"use strict";
var i, j, abs = Math.abs, sin = Math.sin, cos = Math.cos, max = Math.max,
  min = Math.min, ceil = Math.ceil, sqrt = Math.sqrt, pow = Math.pow,
  hexlookup3 = {}, hexlookup2 = {}, hexlookup1 = {
  0:"0,",   1:"17,",  2:"34,",  3:"51,",  4:"68,",  5:"85,",
  6:"102,", 7:"119,", 8:"136,", 9:"153,", a:"170,", A:"170,",
  b:"187,", B:"187,", c:"204,", C:"204,", d:"221,", D:"221,",
  e:"238,", E:"238,", f:"255,", F:"255,"  
  }, Oproto, Tproto, TCproto, Mproto, Vproto, TSproto, TCVproto,
  doc = document, ocanvas, handlers = {};
for(i = 0; i < 256; ++i) {
  j = i.toString(16);
  if(i < 16)
    j = '0' + j;
  hexlookup2[j] = hexlookup2[j.toUpperCase()] = i.toString() + ',';
}
function Defined(d) {
  return typeof d != 'undefined';
}
function IsObject(o) {
  return typeof o == 'object' && o != null;
}
function Clamp(v, mn, mx) {
  return isNaN(v) ? mx : min(mx, max(mn, v));
}
function Nop() {
  return false;
}
function TimeNow() {
  return new Date().valueOf();
}
function SortList(l, f) {
  var nl = [], tl = l.length, i;
  for(i = 0; i < tl; ++i)
    nl.push(l[i]);
  nl.sort(f);
  return nl;
}
function Shuffle(a) {
  var i = a.length-1, t, p;
  while(i) {
    p = ~~(Math.random()*i);
    t = a[i];
    a[i] = a[p];
    a[p] = t;
    --i;
  }
}
function Vector(x, y, z) {
  this.x = x;
  this.y = y;
  this.z = z;
}
Vproto = Vector.prototype;
Vproto.length = function() {
  return sqrt(this.x * this.x + this.y * this.y + this.z * this.z);
};
Vproto.dot = function(v) {
  return this.x * v.x + this.y * v.y + this.z * v.z;
};
Vproto.cross = function(v) {
  var x = this.y * v.z - this.z * v.y,
    y = this.z * v.x - this.x * v.z,
    z = this.x * v.y - this.y * v.x;
  return new Vector(x, y, z);
};
Vproto.angle = function(v) {
  var dot = this.dot(v), ac;
  if(dot == 0)
    return Math.PI / 2.0;
  ac = dot / (this.length() * v.length());
  if(ac >= 1)
    return 0;
  if(ac <= -1)
    return Math.PI;
  return Math.acos(ac);
};
Vproto.unit = function() {
  var l = this.length();
  return new Vector(this.x / l, this.y / l, this.z / l);
};
function MakeVector(lg, lt) {
  lt = lt * Math.PI / 180;
  lg = lg * Math.PI / 180;
  var x = sin(lg) * cos(lt), y = -sin(lt), z = -cos(lg) * cos(lt);
  return new Vector(x, y, z);
}
function Matrix(a) {
  this[1] = {1: a[0],  2: a[1],  3: a[2]};
  this[2] = {1: a[3],  2: a[4],  3: a[5]};
  this[3] = {1: a[6],  2: a[7],  3: a[8]};
}
Mproto = Matrix.prototype;
Matrix.Identity = function() {
  return new Matrix([1,0,0, 0,1,0, 0,0,1]);
};
Matrix.Rotation = function(angle, u) {
  var sina = sin(angle), cosa = cos(angle), mcos = 1 - cosa;
  return new Matrix([
    cosa + pow(u.x, 2) * mcos, u.x * u.y * mcos - u.z * sina, u.x * u.z * mcos + u.y * sina,
    u.y * u.x * mcos + u.z * sina, cosa + pow(u.y, 2) * mcos, u.y * u.z * mcos - u.x * sina,
    u.z * u.x * mcos - u.y * sina, u.z * u.y * mcos + u.x * sina, cosa + pow(u.z, 2) * mcos
  ]);
}
Mproto.mul = function(m) {
  var a = [], i, j, mmatrix = (m.xform ? 1 : 0);
  for(i = 1; i <= 3; ++i)
    for(j = 1; j <= 3; ++j) {
      if(mmatrix)
        a.push(this[i][1] * m[1][j] +
          this[i][2] * m[2][j] +
          this[i][3] * m[3][j]);
      else
        a.push(this[i][j] * m);
    }
  return new Matrix(a);
};
Mproto.xform = function(p) {
  var a = {}, x = p.x, y = p.y, z = p.z;
  a.x = x * this[1][1] + y * this[2][1] + z * this[3][1];
  a.y = x * this[1][2] + y * this[2][2] + z * this[3][2];
  a.z = x * this[1][3] + y * this[2][3] + z * this[3][3];
  return a;
};
function PointsOnSphere(n,xr,yr,zr,magic) {
  var i, y, r, phi, pts = [], off = 2/n, inc;
  inc = Math.PI * (3 - sqrt(5) + (parseFloat(magic) ? parseFloat(magic) : 0));
  for(i = 0; i < n; ++i) {
    y = i * off - 1 + (off / 2);
    r = sqrt(1 - y*y);
    phi = i * inc;
    pts.push([cos(phi) * r * xr, y * yr, sin(phi) * r * zr]);
  }
  return pts;
}
function Cylinder(n,o,xr,yr,zr,magic) {
  var phi, pts = [], off = 2/n, inc, i, j, k, l;
  inc = Math.PI * (3 - sqrt(5) + (parseFloat(magic) ? parseFloat(magic) : 0));
  for(i = 0; i < n; ++i) {
    j = i * off - 1 + (off / 2);
    phi = i * inc;
    k = cos(phi);
    l = sin(phi);
    pts.push(o ? [j * xr, k * yr, l * zr] : [k * xr, j * yr, l * zr]);
  }
  return pts;
}
function Ring(o, n, xr, yr, zr, j) {
  var phi, pts = [], inc = Math.PI * 2 / n, i, k, l;
  for(i = 0; i < n; ++i) {
    phi = i * inc;
    k = cos(phi);
    l = sin(phi);
    pts.push(o ? [j * xr, k * yr, l * zr] : [k * xr, j * yr, l * zr]);
  }
  return pts;
}
function PointsOnCylinderV(n,xr,yr,zr,m) { return Cylinder(n, 0, xr, yr, zr, m) }
function PointsOnCylinderH(n,xr,yr,zr,m) { return Cylinder(n, 1, xr, yr, zr, m) }
function PointsOnRingV(n, xr, yr, zr, offset) {
  offset = isNaN(offset) ? 0 : offset * 1;
  return Ring(0, n, xr, yr, zr, offset);
}
function PointsOnRingH(n, xr, yr, zr, offset) {
  offset = isNaN(offset) ? 0 : offset * 1;
  return Ring(1, n, xr, yr, zr, offset);
}
function CentreImage(t) {
  var i = new Image;
  i.onload = function() {
    var dx = i.width / 2, dy = i.height / 2;
    t.centreFunc = function(c, w, h, cx, cy) {
      c.setTransform(1, 0, 0, 1, 0, 0);
      c.globalAlpha = 1;
      c.drawImage(i, cx - dx, cy - dy);
    };
  };
  i.src = t.centreImage;
}
function SetAlpha(c,a) {
  var d = c, p1, p2, ae = (a*1).toPrecision(3) + ')';
  if(c[0] === '#') {
    if(!hexlookup3[c])
      if(c.length === 4)
        hexlookup3[c] = 'rgba(' + hexlookup1[c[1]] + hexlookup1[c[2]] + hexlookup1[c[3]];
      else
        hexlookup3[c] = 'rgba(' + hexlookup2[c.substr(1,2)] + hexlookup2[c.substr(3,2)] + hexlookup2[c.substr(5,2)];
    d = hexlookup3[c] + ae;
  } else if(c.substr(0,4) === 'rgb(' || c.substr(0,4) === 'hsl(') {
    d = (c.replace('(','a(').replace(')', ',' + ae));
  } else if(c.substr(0,5) === 'rgba(' || c.substr(0,5) === 'hsla(') {
    p1 = c.lastIndexOf(',') + 1, p2 = c.indexOf(')');
    a *= parseFloat(c.substring(p1,p2));
    d = c.substr(0,p1) + a.toPrecision(3) + ')';
  }
  return d;
}
function NewCanvas(w,h) {
  // if using excanvas, give up now
  if(window.G_vmlCanvasManager)
    return null;
  var c = doc.createElement('canvas');
  c.width = w;
  c.height = h;
  return c;
}
// I think all browsers pass this test now...
function ShadowAlphaBroken() {
  var cv = NewCanvas(3,3), c, i;
  if(!cv)
    return false;
  c = cv.getContext('2d');
  c.strokeStyle = '#000';
  c.shadowColor = '#fff';
  c.shadowBlur = 3;
  c.globalAlpha = 0;
  c.strokeRect(2,2,2,2);
  c.globalAlpha = 1;
  i = c.getImageData(2,2,1,1);
  cv = null;
  return (i.data[0] > 0);
}
function SetGradient(c, l, o, g) {
  var gd = c.createLinearGradient(0, 0, l, 0), i;
  for(i in g)
    gd.addColorStop(1 - i, g[i]);
  c.fillStyle = gd;
  c.fillRect(0, o, l, 1);
}
function FindGradientColour(tc, p, r) {
  var l = 1024, h = 1, gl = tc.weightGradient, cv, c, i, d;
  if(tc.gCanvas) {
    c = tc.gCanvas.getContext('2d');
    h = tc.gCanvas.height;
  } else {
    if(IsObject(gl[0]))
      h = gl.length;
    else
      gl = [gl];
    tc.gCanvas = cv = NewCanvas(l, h);
    if(!cv)
      return null;
    c = cv.getContext('2d');
    for(i = 0; i < h; ++i)
      SetGradient(c, l, i, gl[i]);
  }
  r = max(min(r || 0, h - 1), 0);
  d = c.getImageData(~~((l - 1) * p), r, 1, 1).data;
  return 'rgba(' + d[0] + ',' + d[1] + ',' + d[2] + ',' + (d[3]/255) + ')';
}
function TextSet(ctxt, font, colour, strings, padx, pady, shadowColour,
  shadowBlur, shadowOffsets, maxWidth, widths, align) {
  var xo = padx + (shadowBlur || 0) + 
    (shadowOffsets.length && shadowOffsets[0] < 0 ? abs(shadowOffsets[0]) : 0),
    yo = pady + (shadowBlur || 0) + 
    (shadowOffsets.length && shadowOffsets[1] < 0 ? abs(shadowOffsets[1]) : 0), i, xc;
  ctxt.font = font;
  ctxt.textBaseline = 'top';
  ctxt.fillStyle = colour;
  shadowColour && (ctxt.shadowColor = shadowColour);
  shadowBlur && (ctxt.shadowBlur = shadowBlur);
  shadowOffsets.length && (ctxt.shadowOffsetX = shadowOffsets[0],
    ctxt.shadowOffsetY = shadowOffsets[1]);
  for(i = 0; i < strings.length; ++i) {
    xc = 0;
    if(widths) {
      if('right' == align) {
        xc = maxWidth - widths[i];
      } else if('centre' == align) {
        xc = (maxWidth - widths[i]) / 2;
      }
    }
    ctxt.fillText(strings[i], xo + xc, yo);
    yo += parseInt(font);
  }
}
function RRect(c, x, y, w, h, r, s) {
  if(r) {
    c.beginPath();
    c.moveTo(x, y + h - r);
    c.arcTo(x, y, x + r, y, r);
    c.arcTo(x + w, y, x + w, y + r, r);
    c.arcTo(x + w, y + h, x + w - r, y + h, r);
    c.arcTo(x, y + h, x, y + h - r, r);
    c.closePath();
    c[s ? 'stroke' : 'fill']();
  } else {
    c[s ? 'strokeRect' : 'fillRect'](x, y, w, h);
  }
}
function TextCanvas(strings, font, w, h, maxWidth, stringWidths, align, valign,
  scale