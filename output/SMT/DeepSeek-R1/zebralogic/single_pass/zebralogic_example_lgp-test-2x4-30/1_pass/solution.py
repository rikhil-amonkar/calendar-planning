from z3 import *
import json

def main():
    s = Solver()
    
    # Define the attributes for each house
    Name1, Name2 = String('Name1'), String('Name2')
    HairColor1, HairColor2 = String('HairColor1'), String('HairColor2')
    FavoriteSport1, FavoriteSport2 = String('FavoriteSport1'), String('FavoriteSport2')
    Smoothie1, Smoothie2 = String('Smoothie1'), String('Smoothie2')
    
    # Define the possible values for each attribute
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]
    
    # Each attribute must be one of the predefined values
    s.add(Or([Name1 == n for n in names]))
    s.add(Or([Name2 == n for n in names]))
    s.add(Distinct(Name1, Name2))
    
    s.add(Or([HairColor1 == h for h in hair_colors]))
    s.add(Or([HairColor2 == h for h in hair_colors]))
    s.add(Distinct(HairColor1, HairColor2))
    
    s.add(Or([FavoriteSport1 == sp for sp in sports]))
    s.add(Or([FavoriteSport2 == sp for sp in sports]))
    s.add(Distinct(FavoriteSport1, FavoriteSport2))
    
    s.add(Or([Smoothie1 == sm for sm in smoothies]))
    s.add(Or([Smoothie2 == sm for sm in smoothies]))
    s.add(Distinct(Smoothie1, Smoothie2))
    
    # Clue 1: The Desert smoothie lover is Arnold
    s.add(Implies(Smoothie1 == "desert", Name1 == "Arnold"))
    s.add(Implies(Smoothie2 == "desert", Name2 == "Arnold"))
    s.add(Implies(Name1 == "Arnold", Smoothie1 == "desert"))
    s.add(Implies(Name2 == "Arnold", Smoothie2 == "desert"))
    
    # Clue 2: The person with brown hair loves basketball
    s.add((HairColor1 == "brown") == (FavoriteSport1 == "basketball"))
    s.add((HairColor2 == "brown") == (FavoriteSport2 == "basketball"))
    
    # Clue 3: Arnold is to the left of the person with black hair
    s.add(Name1 == "Arnold")
    s.add(HairColor2 == "black")
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract values for house 1
        n1 = str(m[Name1])
        hc1 = str(m[HairColor1])
        fs1 = str(m[FavoriteSport1])
        sm1 = str(m[Smoothie1])
        # Extract values for house 2
        n2 = str(m[Name2])
        hc2 = str(m[HairColor2])
        fs2 = str(m[FavoriteSport2])
        sm2 = str(m[Smoothie2])
        
        # Prepare the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                "rows": [
                    ["1", n1, hc1, fs1, sm1],
                    ["2", n2, hc2, fs2, sm2]
                ]
            }
        }
        print(json.dumps(solution_dict))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()