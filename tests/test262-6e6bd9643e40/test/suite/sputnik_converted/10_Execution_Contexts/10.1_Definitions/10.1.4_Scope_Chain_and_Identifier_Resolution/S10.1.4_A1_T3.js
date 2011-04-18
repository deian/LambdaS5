// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/**
 * @name: S10.1.4_A1_T3;
 * @section: 10.1.4;
 * @assertion: Every execution context has associated with it a scope chain. 
 * A scope chain is a list of objects that are searched when evaluating an 
 * Identifier;
 * @description: Checking scope chain containing function declarations;
*/


// Converted for Test262 from original Sputnik source

ES5Harness.registerTest( {
id: "S10.1.4_A1_T3",

path: "10.1.4",

description: "Checking scope chain containing function declarations",

test: function testcase() {
   var x = 0;

function f1(){
  function f2(){
    return x;
  };
  return f2();
  
  var x = 1;
}

if(!(f1() === undefined)){
  $ERROR("#1: Scope chain disturbed");
}


 }
});

