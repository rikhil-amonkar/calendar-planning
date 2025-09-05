from z3 import *
import json

def main():
    s = Solver()
    
    # Define enums for each category
    Name, (Eric, Arnold, Peter) = EnumSort('Name', ['Eric', 'Arnold', 'Peter'])
    Vacation, (mountain, city, beach) = EnumSort('Vacation', ['mountain', 'city', 'beach'])
    Height, (very_short, average, short) = EnumSort('Height', ['very short', 'average', 'short'])
    Flower, (carnations, daffodils, lilies) = EnumSort('Flower', ['carnations', 'daffodils', 'lilies'])
    HairColor, (brown, black, blonde) = EnumSort('HairColor', ['brown', 'black', 'blonde'])
    Education, (associate, bachelor, high_school) = EnumSort('Education', ['associate', 'bachelor', 'high school'])
    
    # Create attributes for each house (index 0 = house 1, index 1 = house 2, index 2 = house 3)
    names = [Const(f'name_{i}', Name) for i in range(3)]
    vacations = [Const(f'vacation_{i}', Vacation) for i in range(3)]
    heights = [Const(f'height_{i}', Height) for i in range(3)]
    flowers = [Const(f'flower_{i}', Flower) for i in range(3)]
    hairColors = [Const(f'hairColor_{i}', HairColor) for i in range(3)]
    educations = [Const(f'education_{i}', Education) for i in range(3)]
    
    # Add uniqueness constraints
    s.add(Distinct(names))
    s.add(Distinct(vacations))
    s.add(Distinct(heights))
    s.add(Distinct(flowers))
    s.add(Distinct(hairColors))
    s.add(Distinct(educations))
    
    # Clue 1: Peter has average height
    for i in range(3):
        s.add(Implies(names[i] == Peter, heights[i] == average))
    
    # Clue 2: Arnold loves daffodils
    for i in range(3):
        s.add(Implies(flowers[i] == daffodils, names[i] == Arnold))
    
    # Clue 3: Very short not in second house
    s.add(heights[1] != very_short)
    
    # Clue 4: Beach vacation in first house
    s.add(vacations[0] == beach)
    
    # Clue 5: High school diploma in third house
    s.add(educations[2] == high_school)
    
    # Clue 6: Short is right of very short
    very_short_index = Int('very_short_index')
    short_index = Int('short_index')
    s.add(very_short_index >= 0, very_short_index <= 2)
    s.add(short_index >= 0, short_index <= 2)
    for i in range(3):
        s.add(If(heights[i] == very_short, very_short_index == i, True))
        s.add(If(heights[i] == short, short_index == i, True))
    s.add(short_index > very_short_index)
    
    # Clue 7: Eric loves lilies
    for i in range(3):
        s.add(Implies(flowers[i] == lilies, names[i] == Eric))
    
    # Clue 8: Lilies lover has bachelor degree
    for i in range(3):
        s.add(Implies(flowers[i] == lilies, educations[i] == bachelor))
    
    # Clue 9: City breaks right of Peter
    peter_index = Int('peter_index')
    city_index = Int('city_index')
    s.add(peter_index >= 0, peter_index <= 2)
    s.add(city_index >= 0, city_index <= 2)
    for i in range(3):
        s.add(If(names[i] == Peter, peter_index == i, True))
        s.add(If(vacations[i] == city, city_index == i, True))
    s.add(city_index > peter_index)
    
    # Clue 10: Blonde hair in third house
    s.add(hairColors[2] == blonde)
    
    # Clue 11: Beach vacation has brown hair
    s.add(hairColors[0] == brown)
    
    # Check solution
    if s.check() != sat:
        print('{"solution": {}}')
        return
        
    m = s.model()
    
    # Mapping functions
    def get_enum_value(val, enum_list):
        for enum in enum_list:
            if eq(val, enum):
                return enum.decl().name()
        return None
        
    # Collect results
    rows = []
    for i in range(3):
        n_val = m.eval(names[i])
        v_val = m.eval(vacations[i])
        h_val = m.eval(heights[i])
        f_val = m.eval(flowers[i])
        hc_val = m.eval(hairColors[i])
        e_val = m.eval(educations[i])
        
        row = [
            str(i+1),
            get_enum_value(n_val, [Eric, Arnold, Peter]),
            get_enum_value(v_val, [mountain, city, beach]),
            get_enum_value(h_val, [very_short, average, short]),
            get_enum_value(f_val, [carnations, daffodils, lilies]),
            get_enum_value(hc_val, [brown, black, blonde]),
            get_enum_value(e_val, [associate, bachelor, high_school])
        ]
        rows.append(row)
    
    # Format output
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": rows
        }
    }
    print(json.dumps(solution))

if __name__ == "__main__":
    main()