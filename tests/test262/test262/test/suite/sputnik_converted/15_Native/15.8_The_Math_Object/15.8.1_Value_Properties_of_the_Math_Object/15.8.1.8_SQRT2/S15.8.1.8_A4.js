// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/**
 * @name: S15.8.1.8_A4;
 * @section: 15.8.1.8;
 * @assertion: Value Property SQRT2 of the Math Object has the attribute ReadOnly;
 * @description: Checking if Math.SQRT2 property has the attribute ReadOnly;
 * @strict_mode_negative
 */


// Converted for Test262 from original Sputnik source

ES5Harness.registerTest( {
id: "S15.8.1.8_A4",

path: "15_Native\15.8_The_Math_Object\15.8.1_Value_Properties_of_the_Math_Object\15.8.1.8_SQRT2\S15.8.1.8_A4.js",

assertion: "Value Property SQRT2 of the Math Object has the attribute ReadOnly",

description: "Checking if Math.SQRT2 property has the attribute ReadOnly",

test: function testcase() {
   // CHECK#1
var x = Math.SQRT2;
Math.SQRT2 = 1;
if (Math.SQRT2 !== x) {
  $ERROR('#1: Math.SQRT2 hasn\'t ReadOnly: \'x = Math.SQRT2;Math.SQRT2 = 1;Math.SQRT2 === x\'');
}

 }
});
