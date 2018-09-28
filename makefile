modules = \
  src/Proof/Basics.lhs \
  src/Proof/ConjDisj.lhs \
  src/Proof/Equality.lhs \
  src/Proof/ForAll.lhs \
  src/Proof/Exists.lhs \
  src/Proof/Neg.lhs \
  src/Proof/Equiv.lhs \
  src/Functions/IdComp.lhs \
  src/Functions/Const.lhs \
  src/Functions/Flip.lhs \
  src/Functions/Clone.lhs \
  src/Functions/Helpers.lhs \
  src/Booleans.lhs \
  src/Booleans/And.lhs \
  src/Booleans/Or.lhs \
  src/Booleans/Not.lhs \
  src/Booleans/Eq.lhs \
  src/Types/Unit.lhs \
  src/Types/Pair.lhs \
  src/Types/Either.lhs \
  src/Types/Maybe.lhs \
  src/Naturals.lhs \
  src/Naturals/SimpleRecursion.lhs \
  src/Naturals/MutatingRecursion.lhs \
  src/Naturals/Previous.lhs \
  src/Naturals/Plus.lhs \
  src/Naturals/Times.lhs \
  src/Naturals/SimpleEquations.lhs \
  src/Naturals/Minus.lhs \
  src/Naturals/LessThanOrEqualTo.lhs \
  src/Naturals/LessThan.lhs \
  src/Naturals/MaxAndMin.lhs \
  src/Naturals/DivisionAlgorithm.lhs \
  src/Naturals/Divides.lhs

build:
	stack exec site build

watch:
	stack exec site watch

check:
	@mycelium $(modules)
	@unflatten -l 10 -f graph.dot | dot -Tpng -o images/dependency-graph.png
	@rm graph.dot

deploy:
	rm -rf ./docs
	stack exec site clean
	stack exec site build
	cp -r ./_site ./docs
