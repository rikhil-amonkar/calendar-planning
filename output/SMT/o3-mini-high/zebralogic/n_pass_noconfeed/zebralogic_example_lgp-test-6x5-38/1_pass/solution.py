from z3 import *
import json

def main():
    s = Solver()
    
    # Define variables for Names
    Arnold = Int("Arnold")
    Carol = Int("Carol")
    Eric = Int("Eric")
    Bob = Int("Bob")
    Alice = Int("Alice")
    Peter = Int("Peter")
    
    # Define variables for Birthdays
    feb = Int("feb")
    mar = Int("mar")
    sept = Int("sept")
    jan = Int("jan")
    may = Int("may")
    april = Int("april")
    
    # Define variables for Foods
    stew = Int("stew")
    soup = Int("soup")
    grilled_cheese = Int("grilled_cheese")
    stir_fry = Int("stir_fry")
    spaghetti = Int("spaghetti")
    pizza = Int("pizza")
    
    # Define variables for Heights
    very_short = Int("very_short")
    average = Int("average")
    super_tall = Int("super_tall")
    short = Int("short")
    very_tall = Int("very_tall")
    tall = Int("tall")
    
    # Define variables for Car Models
    chevrolet_silverado = Int("chevrolet_silverado")
    ford_f150 = Int("ford_f150")
    bmw_3_series = Int("bmw_3_series")
    tesla_model_3 = Int("tesla_model_3")
    toyota_camry = Int("toyota_camry")
    honda_civic = Int("honda_civic")
    
    # All variables must have values between 1 and 6
    all_vars = [Arnold, Carol, Eric, Bob, Alice, Peter,
                feb, mar, sept, jan, may, april,
                stew, soup, grilled_cheese, stir_fry, spaghetti, pizza,
                very_short, average, super_tall, short, very_tall, tall,
                chevrolet_silverado, ford_f150, bmw_3_series, tesla_model_3, toyota_camry, honda_civic]
    for var in all_vars:
        s.add(var >= 1, var <= 6)
        
    # Add distinct constraints for each category
    s.add(Distinct(Arnold, Carol, Eric, Bob, Alice, Peter))
    s.add(Distinct(feb, mar, sept, jan, may, april))
    s.add(Distinct(stew, soup, grilled_cheese, stir_fry, spaghetti, pizza))
    s.add(Distinct(very_short, average, super_tall, short, very_tall, tall))
    s.add(Distinct(chevrolet_silverado, ford_f150, bmw_3_series, tesla_model_3, toyota_camry, honda_civic))
    
    # Clue 1: The person who owns a Honda Civic is the person who is short.
    s.add(honda_civic == short)
    
    # Clue 2: The person who owns a Ford F-150 is in the fifth house.
    s.add(ford_f150 == 5)
    
    # Clue 3: The person who loves stir fry is somewhere to the left of Eric.
    s.add(stir_fry < Eric)
    
    # Clue 4: The person whose birthday is in May is somewhere to the left of Carol.
    s.add(may < Carol)
    
    # Clue 5: The person who is very short is somewhere to the left of the person whose birthday is in April.
    s.add(very_short < april)
    
    # Clue 6: The person who owns a BMW 3 Series is not in the third house.
    s.add(bmw_3_series != 3)
    
    # Clue 7: There are two houses between the person who loves stir fry and the person who is a pizza lover.
    s.add(Abs(stir_fry - pizza) == 3)
    
    # Clue 8: The person who loves the soup is directly left of Eric.
    s.add(soup + 1 == Eric)
    
    # Clue 9: The person who loves spaghetti and the person whose birthday is in May are next to each other.
    s.add(Abs(spaghetti - may) == 1)
    
    # Clue 10: Alice is directly left of the person who owns a BMW 3 Series.
    s.add(Alice + 1 == bmw_3_series)
    
    # Clue 11: The person who owns a Tesla Model 3 is somewhere to the left of the person who is tall.
    s.add(tesla_model_3 < tall)
    
    # Clue 12: The person who is very tall is the person who owns a Toyota Camry.
    s.add(very_tall == toyota_camry)
    
    # Clue 13: Peter is directly left of the person who is a pizza lover.
    s.add(Peter + 1 == pizza)
    
    # Clue 14: The person who loves the stew is not in the third house.
    s.add(stew != 3)
    
    # Clue 15: There is one house between the person whose birthday is in September and the person who is very short.
    s.add(Abs(sept - very_short) == 2)
    
    # Clue 16: There is one house between the person whose birthday is in March and the person who is super tall.
    s.add(Abs(mar - super_tall) == 2)
    
    # Clue 17: The person who is tall is Bob.
    s.add(tall == Bob)
    
    # Clue 18: The person whose birthday is in May is somewhere to the right of Alice.
    s.add(may > Alice)
    
    # Clue 19: The person who is very short is in the fourth house.
    s.add(very_short == 4)
    
    # Clue 20: The person whose birthday is in March is the person who is short.
    s.add(mar == short)
    
    # Clue 21: Carol is the person who owns a Tesla Model 3.
    s.add(Carol == tesla_model_3)
    
    # Clue 22: Eric is the person whose birthday is in January.
    s.add(Eric == jan)
    
    if s.check() == sat:
        m = s.model()
        
        # Extract the solution for each category
        name_assignments = [
            ("Arnold", m[Arnold].as_long()),
            ("Carol", m[Carol].as_long()),
            ("Eric", m[Eric].as_long()),
            ("Bob", m[Bob].as_long()),
            ("Alice", m[Alice].as_long()),
            ("Peter", m[Peter].as_long())
        ]
        birthday_assignments = [
            ("feb", m[feb].as_long()),
            ("mar", m[mar].as_long()),
            ("sept", m[sept].as_long()),
            ("jan", m[jan].as_long()),
            ("may", m[may].as_long()),
            ("april", m[april].as_long())
        ]
        food_assignments = [
            ("stew", m[stew].as_long()),
            ("soup", m[soup].as_long()),
            ("grilled cheese", m[grilled_cheese].as_long()),
            ("stir fry", m[stir_fry].as_long()),
            ("spaghetti", m[spaghetti].as_long()),
            ("pizza", m[pizza].as_long())
        ]
        height_assignments = [
            ("very short", m[very_short].as_long()),
            ("average", m[average].as_long()),
            ("super tall", m[super_tall].as_long()),
            ("short", m[short].as_long()),
            ("very tall", m[very_tall].as_long()),
            ("tall", m[tall].as_long())
        ]
        car_assignments = [
            ("chevrolet silverado", m[chevrolet_silverado].as_long()),
            ("ford f150", m[ford_f150].as_long()),
            ("bmw 3 series", m[bmw_3_series].as_long()),
            ("tesla model 3", m[tesla_model_3].as_long()),
            ("toyota camry", m[toyota_camry].as_long()),
            ("honda civic", m[honda_civic].as_long())
        ]
        
        # Create a mapping from house number to its attributes
        houses = {i: {"Name": None, "Birthday": None, "Food": None, "Height": None, "CarModel": None} for i in range(1, 7)}
        
        for name, pos in name_assignments:
            houses[pos]["Name"] = name
        for bday, pos in birthday_assignments:
            houses[pos]["Birthday"] = bday
        for food, pos in food_assignments:
            houses[pos]["Food"] = food
        for height, pos in height_assignments:
            houses[pos]["Height"] = height
        for car, pos in car_assignments:
            houses[pos]["CarModel"] = car
        
        # Build rows in order of houses 1 to 6
        rows = []
        for i in range(1, 7):
            row = [
                str(i),
                houses[i]["Name"],
                houses[i]["Birthday"],
                houses[i]["Food"],
                houses[i]["Height"],
                houses[i]["CarModel"]
            ]
            rows.append(row)
        
        output = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
                "rows": rows
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()