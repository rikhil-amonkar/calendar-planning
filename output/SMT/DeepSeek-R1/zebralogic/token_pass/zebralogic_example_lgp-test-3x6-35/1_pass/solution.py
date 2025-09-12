from z3 import *
import json

def main():
    # Define the categories and their values
    Name = Datatype('Name')
    Name.declare('Eric')
    Name.declare('Arnold')
    Name.declare('Peter')
    Name = Name.create()

    Vacation = Datatype('Vacation')
    Vacation.declare('mountain')
    Vacation.declare('city')
    Vacation.declare('beach')
    Vacation = Vacation.create()

    Height = Datatype('Height')
    Height.declare('very_short')
    Height.declare('short')
    Height.declare('average')
    Height = Height.create()

    Flower = Datatype('Flower')
    Flower.declare('carnations')
    Flower.declare('daffodils')
    Flower.declare('lilies')
    Flower = Flower.create()

    HairColor = Datatype('HairColor')
    HairColor.declare('brown')
    HairColor.declare('black')
    HairColor.declare('blonde')
    HairColor = HairColor.create()

    Education = Datatype('Education')
    Education.declare('associate')
    Education.declare('bachelor')
    Education.declare('high_school')
    Education = Education.create()

    # Create solver instance
    s = Solver()

    # Create variables for each house (index 0,1,2 for houses 1,2,3)
    names = [Const(f'name_{i}', Name) for i in range(3)]
    vacations = [Const(f'vacation_{i}', Vacation) for i in range(3)]
    heights = [Const(f'height_{i}', Height) for i in range(3)]
    flowers = [Const(f'flower_{i}', Flower) for i in range(3)]
    hair_colors = [Const(f'hair_color_{i}', HairColor) for i in range(3)]
    educations = [Const(f'education_{i}', Education) for i in range(3)]

    # Add uniqueness constraints for each category
    s.add(Distinct(names))
    s.add(Distinct(vacations))
    s.add(Distinct(heights))
    s.add(Distinct(flowers))
    s.add(Distinct(hair_colors))
    s.add(Distinct(educations))

    # Clue 1: Peter has average height
    for i in range(3):
        s.add(Implies(names[i] == Name.Peter, heights[i] == Height.average))

    # Clue 2: Arnold loves daffodils
    for i in range(3):
        s.add(Implies(flowers[i] == Flower.daffodils, names[i] == Name.Arnold))

    # Clue 3: Very short person is not in house 2
    s.add(heights[1] != Height.very_short)

    # Clue 4: Beach vacation in house 1
    s.add(vacations[0] == Vacation.beach)

    # Clue 5: High school education in house 3
    s.add(educations[2] == Education.high_school)

    # Clue 6: Short person is right of very short person
    very_short_index = Int('very_short_index')
    short_index = Int('short_index')
    s.add(very_short_index >= 0, very_short_index <= 2)
    s.add(short_index >= 0, short_index <= 2)
    for i in range(3):
        s.add(If(heights[i] == Height.very_short, very_short_index == i, True))
        s.add(If(heights[i] == Height.short, short_index == i, True))
    s.add(short_index > very_short_index)

    # Clue 7: Eric loves lilies
    for i in range(3):
        s.add(Implies(flowers[i] == Flower.lilies, names[i] == Name.Eric))

    # Clue 8: Lilies lover has bachelor degree
    for i in range(3):
        s.add(Implies(flowers[i] == Flower.lilies, educations[i] == Education.bachelor))

    # Clue 9: City vacation is right of Peter
    peter_index = Int('peter_index')
    city_index = Int('city_index')
    s.add(peter_index >= 0, peter_index <= 2)
    s.add(city_index >= 0, city_index <= 2)
    for i in range(3):
        s.add(If(names[i] == Name.Peter, peter_index == i, True))
        s.add(If(vacations[i] == Vacation.city, city_index == i, True))
    s.add(city_index > peter_index)

    # Clue 10: Blonde hair in house 3
    s.add(hair_colors[2] == HairColor.blonde)

    # Clue 11: Beach vacation person has brown hair
    s.add(hair_colors[0] == HairColor.brown)

    # Check satisfiability
    if s.check() == sat:
        model = s.model()
        solution_rows = []
        attribute_map = {
            'very_short': 'very short',
            'high_school': 'high school'
        }
        
        for i in range(3):
            n = model.eval(names[i])
            v = model.eval(vacations[i])
            h = model.eval(heights[i])
            f = model.eval(flowers[i])
            hc = model.eval(hair_colors[i])
            e = model.eval(educations[i])
            
            # Convert to string and apply attribute mapping
            n_str = str(n)
            v_str = str(v)
            h_str = str(h)
            f_str = str(f)
            hc_str = str(hc)
            e_str = str(e)
            
            if h_str in attribute_map:
                h_str = attribute_map[h_str]
            if e_str in attribute_map:
                e_str = attribute_map[e_str]
                
            solution_rows.append([str(i+1), n_str, v_str, h_str, f_str, hc_str, e_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()