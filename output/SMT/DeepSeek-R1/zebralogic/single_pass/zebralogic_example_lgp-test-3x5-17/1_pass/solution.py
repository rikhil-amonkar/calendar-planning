from z3 import *

def main():
    # Define the enums for each attribute
    Name = Datatype('Name')
    Name.declare('Eric')
    Name.declare('Arnold')
    Name.declare('Peter')
    Name = Name.create()
    
    PhoneModel = Datatype('PhoneModel')
    PhoneModel.declare('iphone13')
    PhoneModel.declare('samsung_galaxy_s21')
    PhoneModel.declare('google_pixel_6')
    PhoneModel = PhoneModel.create()
    
    Height = Datatype('Height')
    Height.declare('very_short')
    Height.declare('short')
    Height.declare('average')
    Height = Height.create()
    
    HouseStyle = Datatype('HouseStyle')
    HouseStyle.declare('colonial')
    HouseStyle.declare('ranch')
    HouseStyle.declare('victorian')
    HouseStyle = HouseStyle.create()
    
    CarModel = Datatype('CarModel')
    CarModel.declare('tesla_model_3')
    CarModel.declare('toyota_camry')
    CarModel.declare('ford_f150')
    CarModel = CarModel.create()
    
    # Create arrays for each attribute for the three houses (index 0: house1, 1: house2, 2: house3)
    names = [Const('name_%d' % i, Name) for i in range(3)]
    phones = [Const('phone_%d' % i, PhoneModel) for i in range(3)]
    heights = [Const('height_%d' % i, Height) for i in range(3)]
    house_styles = [Const('house_style_%d' % i, HouseStyle) for i in range(3)]
    car_models = [Const('car_model_%d' % i, CarModel) for i in range(3)]
    
    s = Solver()
    
    # All attributes must be distinct in their category
    s.add(Distinct(names))
    s.add(Distinct(phones))
    s.add(Distinct(heights))
    s.add(Distinct(house_styles))
    s.add(Distinct(car_models))
    
    # Clue 1: Peter is somewhere to the right of Eric.
    # Which means: Eric must be in a lower-numbered house than Peter.
    eric_index = Int('eric_index')
    peter_index = Int('peter_index')
    s.add(eric_index >= 1, eric_index <= 3)
    s.add(peter_index >= 1, peter_index <= 3)
    s.add(peter_index > eric_index)
    for i in range(3):
        s.add(If(names[i] == Name.Eric, eric_index == i+1, True))
        s.add(If(names[i] == Name.Peter, peter_index == i+1, True))
    
    # Clue 2: The person living in a colonial-style house is in the second house.
    s.add(house_styles[1] == HouseStyle.colonial)
    
    # Clue 3: The person who owns a Tesla Model 3 is the person who is very short.
    for i in range(3):
        s.add( (car_models[i] == CarModel.tesla_model_3) == (heights[i] == Height.very_short) )
    
    # Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21.
    s.add( Or(
        And(heights[0] == Height.short, phones[1] == PhoneModel.samsung_galaxy_s21),
        And(heights[1] == Height.short, phones[2] == PhoneModel.samsung_galaxy_s21)
    ) )
    
    # Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
    s.add( Or(
        And(phones[0] == PhoneModel.iphone13, phones[1] == PhoneModel.google_pixel_6),
        And(phones[1] == PhoneModel.iphone13, phones[2] == PhoneModel.google_pixel_6)
    ) )
    
    # Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
    # Since colonial is in house2 (index1), ranch must be in house1 (index0).
    s.add(house_styles[0] == HouseStyle.ranch)
    
    # Clue 7: Arnold is in the second house.
    s.add(names[1] == Name.Arnold)
    
    # Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
    toyota_index = Int('toyota_index')
    ford_index = Int('ford_index')
    s.add(toyota_index >= 1, toyota_index <= 3)
    s.add(ford_index >= 1, ford_index <= 3)
    s.add(ford_index > toyota_index)
    for i in range(3):
        s.add(If(car_models[i] == CarModel.toyota_camry, toyota_index == i+1, True))
        s.add(If(car_models[i] == CarModel.ford_f150, ford_index == i+1, True))
    
    # Clue 9: The person who has an average height is in the first house.
    s.add(heights[0] == Height.average)
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        
        # Mapping from Z3 constants to the required output strings
        name_map = {
            Name.Eric: "Eric",
            Name.Arnold: "Arnold",
            Name.Peter: "Peter"
        }
        phone_map = {
            PhoneModel.iphone13: "iphone 13",
            PhoneModel.samsung_galaxy_s21: "samsung galaxy s21",
            PhoneModel.google_pixel_6: "google pixel 6"
        }
        height_map = {
            Height.very_short: "very short",
            Height.short: "short",
            Height.average: "average"
        }
        house_style_map = {
            HouseStyle.colonial: "colonial",
            HouseStyle.ranch: "ranch",
            HouseStyle.victorian: "victorian"
        }
        car_model_map = {
            CarModel.tesla_model_3: "tesla model 3",
            CarModel.toyota_camry: "toyota camry",
            CarModel.ford_f150: "ford f150"
        }
        
        # Extract values for each house
        rows = []
        for i in range(3):
            n = model.eval(names[i])
            p = model.eval(phones[i])
            h = model.eval(heights[i])
            hs = model.eval(house_styles[i])
            c = model.eval(car_models[i])
            
            row = [
                str(i+1),
                name_map[n.as_long()],
                phone_map[p.as_long()],
                height_map[h.as_long()],
                house_style_map[hs.as_long()],
                car_model_map[c.as_long()]
            ]
            rows.append(row)
        
        # Format the solution as JSON
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                "rows": rows
            }
        }
        
        # Output as JSON string (but the problem requires a dictionary for the program, but note: the problem says output should be JSON-formatted dictionary, so we return the dictionary)
        # However, the problem says the output must be valid JSON that can be parsed by Python's json module. 
        # But since we are writing a Python program, we can output the dictionary and then use json.dumps if needed? 
        # But the problem says: "Your output should be a JSON-formatted dictionary", meaning the program should output the dictionary structure.
        # And the example output is a dictionary. So we return the dictionary.
        # But note: the problem says "Write a Python program that solves it using the Z3 solver", so we just need to print the dictionary?
        # Actually, the problem does not specify how to output. But the structure must be as described.
        # We'll return the dictionary from the function and then print it as JSON string? 
        # However, the problem says: "Always surround your final code with