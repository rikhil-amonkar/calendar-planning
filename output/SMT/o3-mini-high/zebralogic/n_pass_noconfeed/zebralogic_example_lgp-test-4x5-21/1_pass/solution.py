from z3 import *
import json

def main():
    s = Solver()
    
    # Define variables for each category (values 1-4 represent house positions)
    # Names
    house_Eric = Int('house_Eric')
    house_Alice = Int('house_Alice')
    house_Peter = Int('house_Peter')
    house_Arnold = Int('house_Arnold')
    
    # Smoothies
    sm_dragonfruit = Int('sm_dragonfruit')
    sm_cherry = Int('sm_cherry')
    sm_desert = Int('sm_desert')
    sm_watermelon = Int('sm_watermelon')
    
    # Favorite Sports
    sp_soccer = Int('sp_soccer')
    sp_tennis = Int('sp_tennis')
    sp_basketball = Int('sp_basketball')
    sp_swimming = Int('sp_swimming')
    
    # Car Models
    car_tesla = Int('car_tesla')     # "tesla model 3"
    car_toyota = Int('car_toyota')     # "toyota camry"
    car_honda = Int('car_honda')       # "honda civic"
    car_ford = Int('car_ford')         # "ford f150"
    
    # Flowers
    flower_daffodils = Int('flower_daffodils')
    flower_roses = Int('flower_roses')
    flower_lilies = Int('flower_lilies')
    flower_carnations = Int('flower_carnations')
    
    # List of all variables for domain constraints
    all_vars = [
        house_Eric, house_Alice, house_Peter, house_Arnold,
        sm_dragonfruit, sm_cherry, sm_desert, sm_watermelon,
        sp_soccer, sp_tennis, sp_basketball, sp_swimming,
        car_tesla, car_toyota, car_honda, car_ford,
        flower_daffodils, flower_roses, flower_lilies, flower_carnations
    ]
    for var in all_vars:
        s.add(And(var >= 1, var <= 4))
        
    # Add distinct constraints for each category
    s.add(Distinct(house_Eric, house_Alice, house_Peter, house_Arnold))
    s.add(Distinct(sm_dragonfruit, sm_cherry, sm_desert, sm_watermelon))
    s.add(Distinct(sp_soccer, sp_tennis, sp_basketball, sp_swimming))
    s.add(Distinct(car_tesla, car_toyota, car_honda, car_ford))
    s.add(Distinct(flower_daffodils, flower_roses, flower_lilies, flower_carnations))
    
    # Puzzle Constraints
    
    # 1. The person who owns a Tesla Model 3 is the person who loves the rose bouquet.
    s.add(car_tesla == flower_roses)
    
    # 2. Peter is the Dragonfruit smoothie lover.
    s.add(house_Peter == sm_dragonfruit)
    
    # 3. The Desert smoothie lover is the person who owns a Toyota Camry.
    s.add(sm_desert == car_toyota)
    
    # 4. The person who loves tennis is in the first house.
    s.add(sp_tennis == 1)
    
    # 5. The person who owns a Toyota Camry and the person who loves basketball are next to each other.
    s.add(Abs(car_toyota - sp_basketball) == 1)
    
    # 6. Arnold is the person who loves basketball.
    s.add(house_Arnold == sp_basketball)
    
    # 7. The person who owns a Honda Civic is the person who loves a bouquet of daffodils.
    s.add(car_honda == flower_daffodils)
    
    # 8. Eric is the person who loves the rose bouquet.
    s.add(house_Eric == flower_roses)
    
    # 9. The Watermelon smoothie lover is not in the first house.
    s.add(sm_watermelon != 1)
    
    # 10. The person who owns a Honda Civic is somewhere to the right of the Desert smoothie lover.
    s.add(car_honda > sm_desert)
    
    # 11. The person who loves basketball is the person who loves the bouquet of lilies.
    s.add(sp_basketball == flower_lilies)
    
    # 12. The person who loves tennis and the person who loves soccer are next to each other.
    s.add(Abs(sp_tennis - sp_soccer) == 1)
    
    # Solve the puzzle
    if s.check() == sat:
        m = s.model()
        
        # Create a dictionary mapping each house number (1 to 4) to its attributes.
        houses = { i: {} for i in range(1, 5) }
        
        # Map Names to houses
        assignments_names = [
            (m[house_Eric].as_long(), "Eric"),
            (m[house_Alice].as_long(), "Alice"),
            (m[house_Peter].as_long(), "Peter"),
            (m[house_Arnold].as_long(), "Arnold")
        ]
        for pos, name in assignments_names:
            houses[pos]["Name"] = name
        
        # Map Smoothies to houses
        assignments_smoothies = [
            (m[sm_dragonfruit].as_long(), "dragonfruit"),
            (m[sm_cherry].as_long(), "cherry"),
            (m[sm_desert].as_long(), "desert"),
            (m[sm_watermelon].as_long(), "watermelon")
        ]
        for pos, smoothie in assignments_smoothies:
            houses[pos]["Smoothie"] = smoothie
        
        # Map Favorite Sports to houses
        assignments_sports = [
            (m[sp_soccer].as_long(), "soccer"),
            (m[sp_tennis].as_long(), "tennis"),
            (m[sp_basketball].as_long(), "basketball"),
            (m[sp_swimming].as_long(), "swimming")
        ]
        for pos, sport in assignments_sports:
            houses[pos]["FavoriteSport"] = sport
        
        # Map Car Models to houses
        assignments_cars = [
            (m[car_tesla].as_long(), "tesla model 3"),
            (m[car_toyota].as_long(), "toyota camry"),
            (m[car_honda].as_long(), "honda civic"),
            (m[car_ford].as_long(), "ford f150")
        ]
        for pos, car in assignments_cars:
            houses[pos]["CarModel"] = car
        
        # Map Flowers to houses
        assignments_flowers = [
            (m[flower_daffodils].as_long(), "daffodils"),
            (m[flower_roses].as_long(), "roses"),
            (m[flower_lilies].as_long(), "lilies"),
            (m[flower_carnations].as_long(), "carnations")
        ]
        for pos, flower in assignments_flowers:
            houses[pos]["Flower"] = flower
        
        # Build rows in order of houses 1 to 4 with the required header order
        rows = []
        for i in range(1, 5):
            row = [
                str(i),
                houses[i].get("Name", ""),
                houses[i].get("Smoothie", ""),
                houses[i].get("FavoriteSport", ""),
                houses[i].get("CarModel", ""),
                houses[i].get("Flower", "")
            ]
            rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                "rows": rows
            }
        }
        print(json.dumps(result))
        
if __name__ == "__main__":
    main()