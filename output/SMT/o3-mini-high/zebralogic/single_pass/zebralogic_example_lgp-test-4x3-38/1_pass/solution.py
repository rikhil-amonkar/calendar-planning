from z3 import Solver, Int, Distinct, Or, sat
import json

def main():
    s = Solver()

    # Create variables for each person's house (1..4)
    pAlice   = Int("pAlice")
    pPeter   = Int("pPeter")
    pArnold  = Int("pArnold")
    pEric    = Int("pEric")
    
    # Create variables for each mother's associated house
    mHolly   = Int("mHolly")
    mKailyn  = Int("mKailyn")
    mJanelle = Int("mJanelle")
    mAniya   = Int("mAniya")
    
    # Create variables for each flower's associated house
    fCarnations  = Int("fCarnations")
    fRoses       = Int("fRoses")
    fLilies      = Int("fLilies")
    fDaffodils   = Int("fDaffodils")
    
    houses = (1, 2, 3, 4)
    all_vars = [pAlice, pPeter, pArnold, pEric, mHolly, mKailyn, mJanelle, mAniya, fCarnations, fRoses, fLilies, fDaffodils]

    # All variables must be in the range 1..4
    for var in all_vars:
        s.add(Or(var == 1, var == 2, var == 3, var == 4))
    
    # Each person is in a unique house.
    s.add(Distinct(pAlice, pPeter, pArnold, pEric))
    # Each mother is associated with a unique house.
    s.add(Distinct(mHolly, mKailyn, mJanelle, mAniya))
    # Each flower is associated with a unique house.
    s.add(Distinct(fCarnations, fRoses, fLilies, fDaffodils))
    
    # Clue 8: Alice is in the third house.
    s.add(pAlice == 3)
    
    # Clue 1: Alice is the person whose mother's name is Kailyn.
    s.add(mKailyn == pAlice)
    
    # Clue 5: Arnold is the person whose mother's name is Holly.
    s.add(mHolly == pArnold)
    
    # Clue 4: Eric is the person who loves a bouquet of daffodils.
    s.add(fDaffodils == pEric)
    
    # Clue 7: The person who loves the bouquet of lilies is directly left of Alice.
    s.add(fLilies == pAlice - 1)
    
    # Clue 2: The person whose mother's name is Janelle is somewhere to the right of Arnold.
    s.add(mJanelle > pArnold)
    
    # Clue 3: Peter is somewhere to the right of the person who loves a carnations arrangement.
    s.add(pPeter > fCarnations)
    
    # Clue 6: The person who loves a carnations arrangement is somewhere to the right of the person whose mother's name is Holly.
    s.add(fCarnations > mHolly)
    
    if s.check() == sat:
        m = s.model()
        
        # Create mappings for each house from the solved model.
        persons = {}
        persons[m[pAlice].as_long()]  = "Alice"
        persons[m[pPeter].as_long()]  = "Peter"
        persons[m[pArnold].as_long()] = "Arnold"
        persons[m[pEric].as_long()]   = "Eric"
        
        mothers = {}
        mothers[m[mHolly].as_long()]   = "Holly"
        mothers[m[mKailyn].as_long()]  = "Kailyn"
        mothers[m[mJanelle].as_long()] = "Janelle"
        mothers[m[mAniya].as_long()]   = "Aniya"
        
        flowers = {}
        flowers[m[fCarnations].as_long()] = "carnations"
        flowers[m[fRoses].as_long()]      = "roses"
        flowers[m[fLilies].as_long()]     = "lilies"
        flowers[m[fDaffodils].as_long()]  = "daffodils"
        
        rows = []
        for house in sorted(houses):
            row = [str(house), persons[house], mothers[house], flowers[house]]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Flower"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()