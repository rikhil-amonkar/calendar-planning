from z3 import *
import json

def main():
    s = Solver()

    # Define integer variables for each category (their values represent the house number 1..4).
    # Names
    Eric   = Int('Eric')
    Alice  = Int('Alice')
    Peter  = Int('Peter')
    Arnold = Int('Arnold')
    
    # Smoothies
    dragonfruit = Int('dragonfruit')
    cherry      = Int('cherry')
    desert      = Int('desert')
    watermelon  = Int('watermelon')
    
    # Sports
    soccer     = Int('soccer')
    tennis     = Int('tennis')
    basketball = Int('basketball')
    swimming   = Int('swimming')
    
    # Car Models
    tesla  = Int('tesla')
    toyota = Int('toyota')
    honda  = Int('honda')
    ford   = Int('ford')
    
    # Flowers
    daffodils  = Int('daffodils')
    roses      = Int('roses')
    lilies     = Int('lilies')
    carnations = Int('carnations')
    
    # All variables take values 1..4 (houses numbered 1 to 4)
    variables = [Eric, Alice, Peter, Arnold,
                 dragonfruit, cherry, desert, watermelon,
                 soccer, tennis, basketball, swimming,
                 tesla, toyota, honda, ford,
                 daffodils, roses, lilies, carnations]
    for var in variables:
        s.add(var >= 1, var <= 4)
    
    # Each category must assign a different house to each attribute.
    s.add(Distinct(Eric, Alice, Peter, Arnold))
    s.add(Distinct(dragonfruit, cherry, desert, watermelon))
    s.add(Distinct(soccer, tennis, basketball, swimming))
    s.add(Distinct(tesla, toyota, honda, ford))
    s.add(Distinct(daffodils, roses, lilies, carnations))
    
    # Add the clues as constraints:
    # 1. The person who owns a Tesla Model 3 is the person who loves the rose bouquet.
    s.add(tesla == roses)
    
    # 2. Peter is the Dragonfruit smoothie lover.
    s.add(Peter == dragonfruit)
    
    # 3. The Desert smoothie lover is the person who owns a Toyota Camry.
    s.add(desert == toyota)
    
    # 4. The person who loves tennis is in the first house.
    s.add(tennis == 1)
    
    # 5. The person who owns a Toyota Camry and the person who loves basketball are next to each other.
    s.add(Abs(toyota - basketball) == 1)
    
    # 6. Arnold is the person who loves basketball.
    s.add(Arnold == basketball)
    
    # 7. The person who owns a Honda Civic is the person who loves a bouquet of daffodils.
    s.add(honda == daffodils)
    
    # 8. Eric is the person who loves the rose bouquet.
    s.add(Eric == roses)
    
    # 9. The Watermelon smoothie lover is not in the first house.
    s.add(watermelon != 1)
    
    # 10. The person who owns a Honda Civic is somewhere to the right of the Desert smoothie lover.
    s.add(honda > desert)
    
    # 11. The person who loves basketball is the person who loves the bouquet of lilies.
    s.add(basketball == lilies)
    
    # 12. The person who loves tennis and the person who loves soccer are next to each other.
    s.add(Abs(tennis - soccer) == 1)
    # Given tennis is in house 1, this forces soccer to be house 2.
    s.add(soccer == 2)
    
    # Check and retrieve a solution.
    if s.check() == sat:
        m = s.model()
        # Build dictionaries mapping house numbers to the label for each category.
        name_mapping = {
            m[Eric].as_long(): "Eric",
            m[Alice].as_long(): "Alice",
            m[Peter].as_long(): "Peter",
            m[Arnold].as_long(): "Arnold"
        }
        smoothie_mapping = {
            m[dragonfruit].as_long(): "dragonfruit",
            m[cherry].as_long(): "cherry",
            m[desert].as_long(): "desert",
            m[watermelon].as_long(): "watermelon"
        }
        sport_mapping = {
            m[soccer].as_long(): "soccer",
            m[tennis].as_long(): "tennis",
            m[basketball].as_long(): "basketball",
            m[swimming].as_long(): "swimming"
        }
        car_mapping = {
            m[tesla].as_long(): "tesla model 3",
            m[toyota].as_long(): "toyota camry",
            m[honda].as_long(): "honda civic",
            m[ford].as_long(): "ford f150"
        }
        flower_mapping = {
            m[daffodils].as_long(): "daffodils",
            m[roses].as_long(): "roses",
            m[lilies].as_long(): "lilies",
            m[carnations].as_long(): "carnations"
        }
    
        # Assemble the rows ordered by house number 1 to 4.
        rows = []
        for house in range(1, 5):
            row = [
                str(house),
                name_mapping[house],
                smoothie_mapping[house],
                sport_mapping[house],
                car_mapping[house],
                flower_mapping[house]
            ]
            rows.append(row)
    
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()