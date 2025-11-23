from biodivine_aeon import *
import biodivine_aeon
import sys

biodivine_aeon.LOG_LEVEL = biodivine_aeon.LOG_ESSENTIAL

# This script computes the fixed-points of a single, 
# fully specified Boolean network.
# 
# It either prints the number of solutions, or the
# fist N solutions, assuming N is given as a second argument.
#
# Note that if the network has constant nodes, we can automatically
# percolate them without changing the outcome. However, this is not
# enabled by default to ensure all nodes are present in the result.
# You can uncomment this modification below. 
# 
# Also note that computing only first X fixed-points is not faster
# than computing the total cardinality of the set. I.e. the 
# "time to first" and "time to all" is the same for this implementation.
#
# You can use `.aeon`, `.bnet`, or `.sbml` as input model formats.

bn = BooleanNetwork.from_file(sys.argv[1])
bn = bn.infer_valid_graph()

# If you want to inline constant input nodes, uncomment this line:
#bn = bn.inline_constants(infer_constants=True, repair_graph=True)

limit = None
if len(sys.argv) == 3:
	limit = int(sys.argv[2])

stg = AsynchronousGraph(bn)

# Assert that the network is fully specified.
assert stg.mk_unit_colors().cardinality() == 1

fixed = FixedPoints.symbolic(stg)

if limit is None:
	print(f"2-valued interpretations: {fixed.cardinality()}")
else:
	count = 0
	for r in fixed.vertices():
		print(r.to_named_dict())
		count += 1
		if count >= limit:
			break



