// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/**
* @name: S15.2.4.2_A1;
* @section: 15.2.4.2;
* @assertion: When the toString method is called, the following steps are taken:
* i) Get the [[Class]] property of this object
* ii) Compute a string value by concatenating the three strings "[object ", Result(1), and "]"
* iii) Return Result(2);
* @description: Checking the type of Object.prototype.toString and the returned result; 
*/


// Converted for Test262 from original Sputnik source

ES5Harness.registerTest( {
id: "S15.2.4.2_A1",

path: "15.2.4.2",

description: "Checking the type of Object.prototype.toString and the returned result",

test: function testcase() {
   //CHECK#1
if (typeof Object.prototype.toString !== "function") {
  $ERROR('#1: toString method defined');
}

//CHECK#2
if (Object.prototype.toString() !=="[object "+"Object"+"]") {
  $ERROR('#2: return a string value by concatenating the three strings "[object ", the [[Class]] property of this object, and "]"');
}

//CHECK#3
if ({}.toString()!=="[object "+"Object"+"]") {
  $ERROR('#3: return a string value by concatenating the three strings "[object ", the [[Class]] property of this object, and "]"');
}

 }
});

