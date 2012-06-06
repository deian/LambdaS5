#!/bin/bash

# Run this to update the test results after updating code or test262
sh test262.sh > test-results.txt

grep -A 4 "Summary" test-results.txt > results-summary.txt
