modules = \
  src/Proof/Basics.lhs \
  src/Proof/ConjDisj.lhs \
  src/Proof/Equality.lhs \
  src/Proof/ForAll.lhs \
  src/Proof/Neg.lhs \
  src/Proof/Equiv.lhs \
  src/Functions/IdComp.lhs \
  src/Functions/Const.lhs \
  src/Functions/Flip.lhs \
  src/Functions/Clone.lhs \
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
  src/Naturals/Previous.lhs \
  src/Naturals/Plus.lhs

build:
	stack exec site build

watch:
	stack exec site watch

check:
	@mycelium $(modules)

deploy:
	rm -rf ./docs
	stack exec site build
	mv ./_site ./docs
	stack exec site clean
	stack exec site build
