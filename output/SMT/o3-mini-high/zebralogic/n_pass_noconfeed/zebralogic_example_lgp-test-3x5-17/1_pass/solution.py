from z3 import *
import json

def solve_puzzle():
    s = Solver()
    
    # Define integer variables for each attribute; each variable's value represents the house number (1, 2, or 3).
    # Names
    Eric = Int('Eric')
    Arnold = Int('Arnold')
    Peter = Int('Peter')
    
    # Phone models
    iphone = Int('iphone')
    samsung = Int('samsung')
    google = Int('google')
    
    # Heights
    very_short = Int('very_short')
    average = Int('average')
    short = Int('short')
    
    # House styles
    colonial = Int('colonial')
    ranch = Int('ranch')
    victorian = Int('victorian')
    
    # Car models
    tesla = Int('tesla')
    toyota = Int('toyota')
    ford = Int('ford')
    
    # List all variables for domain restrictions.
    variables = [Eric, Arnold, Peter, iphone, samsung, google,
                 very_short, average, short, colonial, ranch, victorian,
                 tesla, toyota, ford]
    
    for var in variables:
        s.add(var >= 1, var <= 3)
    
    # All attributes in each category must be assigned to different houses.
    s.add(Distinct(Eric, Arnold, Peter))
    s.add(Distinct(iphone, samsung, google))
    s.add(Distinct(very_short, average, short))
    s.add(Distinct(colonial, ranch, victorian))
    s.add(Distinct(tesla, toyota, ford))
    
    # Puzzle constraints based on the clues:
    
    # 1. Peter is somewhere to the right of Eric.
    s.add(Peter > Eric)
    
    # 2. The person living in a colonial-style house is in the second house.
    s.add(colonial == 2)
    
    # 3. The person who owns a Tesla Model 3 is the person who is very short.
    s.add(tesla == very_short)
    
    # 4. The person who is short is directly left of the person who uses a Samsung Galaxy S21.
    s.add(short + 1 == samsung)
    
    # 5. The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
    s.add(iphone + 1 == google)
    
    # 6. The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
    s.add(colonial > ranch)
    
    # 7. Arnold is in the second house.
    s.add(Arnold == 2)
    
    # 8. The person who owns a Ford F150 is somewhere to the right of the person who owns a Toyota Camry.
    s.add(ford > toyota)
    
    # 9. The person who has an average height is in the first house.
    s.add(average == 1)
    
    if s.check() == sat:
        m = s.model()
        # Prepare mappings from house numbers to each attribute.
        houses = {1: {}, 2: {}, 3: {}}
        
        # Names
        names = [("Eric", m[Eric].as_long()),
                 ("Arnold", m[Arnold].as_long()),
                 ("Peter", m[Peter].as_long())]
        for name, pos in names:
            houses[pos]["Name"] = name
        
        # Phone Models
        phones = [("iphone 13", m[iphone].as_long()),
                  ("samsung galaxy s21", m[samsung].as_long()),
                  ("google pixel 6", m[google].as_long())]
        for phone, pos in phones:
            houses[pos]["PhoneModel"] = phone
        
        # Heights
        heights = [("very short", m[very_short].as_long()),
                   ("average", m[average].as_long()),
                   ("short", m[short].as_long())]
        for h, pos in heights:
            houses[pos]["Height"] = h
        
        # House Styles
        styles = [("colonial", m[colonial].as_long()),
                  ("ranch", m[ranch].as_long()),
                  ("victorian", m[victorian].as_long())]
        for style, pos in styles:
            houses[pos]["HouseStyle"] = style
        
        # Car Models
        cars = [("tesla model 3", m[tesla].as_long()),
                ("toyota camry", m[toyota].as_long()),
                ("ford f150", m[ford].as_long())]
        for car, pos in cars:
            houses[pos]["CarModel"] = car
        
        # Assemble the JSON structure with header and rows in order of houses 1 to 3.
        header = ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"]
        rows = []
        for i in range(1, 4):
            row = [
                str(i),
                houses[i]["Name"],
                houses[i]["PhoneModel"],
                houses[i]["Height"],
                houses[i]["HouseStyle"],
                houses[i]["CarModel"]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    solve_puzzle()