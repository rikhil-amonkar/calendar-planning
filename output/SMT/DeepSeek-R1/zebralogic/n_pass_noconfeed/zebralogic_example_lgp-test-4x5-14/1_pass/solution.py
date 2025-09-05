import json
from z3 import *

def main():
    # Define enums and constants for each attribute
    NameEnum, (Peter, Alice, Eric, Arnold) = EnumSort('Name', ['Peter', 'Alice', 'Eric', 'Arnold'])
    MotherEnum, (Janelle, Holly, Aniya, Kailyn) = EnumSort('Mother', ['Janelle', 'Holly', 'Aniya', 'Kailyn'])
    SmoothieEnum, (watermelon, dragonfruit, desert, cherry) = EnumSort('Smoothie', ['watermelon', 'dragonfruit', 'desert', 'cherry'])
    HeightEnum, (tall, average, short, very_short) = EnumSort('Height', ['tall', 'average', 'short', 'very short'])
    EducationEnum, (high_school, associate, master, bachelor) = EnumSort('Education', ['high school', 'associate', 'master', 'bachelor'])
    
    # Create arrays for attributes for each house (0-indexed: house0 = house1, house1 = house2, etc.)
    names = [Const(f'name_{i}', NameEnum) for i in range(4)]
    mothers = [Const(f'mother_{i}', MotherEnum) for i in range(4)]
    smoothies = [Const(f'smoothie_{i}', SmoothieEnum) for i in range(4)]
    heights = [Const(f'height_{i}', HeightEnum) for i in range(4)]
    educations = [Const(f'education_{i}', EducationEnum) for i in range(4)]
    
    s = Solver()
    
    # Add distinct constraints for each attribute category
    s.add(Distinct(names))
    s.add(Distinct(mothers))
    s.add(Distinct(smoothies))
    s.add(Distinct(heights))
    s.add(Distinct(educations))
    
    # Clue 1: Mother Janelle is in third house
    s.add(mothers[2] == Janelle)
    
    # Clue 2: Desert smoothie lover has master's degree
    for i in range(4):
        s.add((smoothies[i] == desert) == (educations[i] == master))
    
    # Clue 3: Desert smoothie not in first house
    s.add(smoothies[0] != desert)
    
    # Clue 4: Very short left of high school diploma
    very_short_house = Int('very_short_house')
    high_school_house = Int('high_school_house')
    s.add(very_short_house >= 0, very_short_house < 4)
    s.add(high_school_house >= 0, high_school_house < 4)
    for i in range(4):
        s.add(If(heights[i] == very_short, very_short_house == i, True))
        s.add(If(educations[i] == high_school, high_school_house == i, True))
    s.add(very_short_house < high_school_house)
    
    # Clue 5: Eric and Cherry smoothie lover are adjacent
    eric_house = Int('eric_house')
    cherry_house = Int('cherry_house')
    s.add(eric_house >= 0, eric_house < 4)
    s.add(cherry_house >= 0, cherry_house < 4)
    for i in range(4):
        s.add(If(names[i] == Eric, eric_house == i, True))
        s.add(If(smoothies[i] == cherry, cherry_house == i, True))
    s.add(Or(eric_house == cherry_house + 1, eric_house == cherry_house - 1))
    
    # Clue 6: High school diploma not in third house
    s.add(educations[2] != high_school)
    
    # Clue 7: Mother Kailyn has associate degree
    for i in range(4):
        s.add((mothers[i] == Kailyn) == (educations[i] == associate))
    
    # Clue 8: Cherry smoothie lover has mother Aniya
    for i in range(4):
        s.add((smoothies[i] == cherry) == (mothers[i] == Aniya))
    
    # Clue 9: Tall person has mother Janelle (already in house 3)
    s.add(heights[2] == tall)
    
    # Clue 10: Arnold right of average height person
    arnold_house = Int('arnold_house')
    average_house = Int('average_house')
    s.add(arnold_house >= 0, arnold_house < 4)
    s.add(average_house >= 0, average_house < 4)
    for i in range(4):
        s.add(If(names[i] == Arnold, arnold_house == i, True))
        s.add(If(heights[i] == average, average_house == i, True))
    s.add(arnold_house > average_house)
    
    # Clue 11: Dragonfruit smoothie directly left of short person
    for i in range(3):
        s.add(Implies(smoothies[i] == dragonfruit, heights[i+1] == short))
    
    # Clue 12: Tall person is Alice (already in house 3)
    s.add(names[2] == Alice)
    
    # Check satisfiability and get model
    if s.check() == sat:
        m = s.model()
        header = ["House", "Name", "Mother", "Smoothie", "Height", "Education"]
        rows = []
        for i in range(4):
            # Evaluate each attribute for the current house
            name_val = m.eval(names[i])
            mother_val = m.eval(mothers[i])
            smoothie_val = m.eval(smoothies[i])
            height_val = m.eval(heights[i])
            education_val = m.eval(educations[i])
            
            # Convert enum values to strings
            name_str = "Peter" if name_val == Peter else "Alice" if name_val == Alice else "Eric" if name_val == Eric else "Arnold"
            mother_str = "Janelle" if mother_val == Janelle else "Holly" if mother_val == Holly else "Aniya" if mother_val == Aniya else "Kailyn"
            smoothie_str = "watermelon" if smoothie_val == watermelon else "dragonfruit" if smoothie_val == dragonfruit else "desert" if smoothie_val == desert else "cherry"
            height_str = "tall" if height_val == tall else "average" if height_val == average else "short" if height_val == short else "very short"
            education_str = "high school" if education_val == high_school else "associate" if education_val == associate else "master" if education_val == master else "bachelor"
            
            rows.append([str(i+1), name_str, mother_str, smoothie_str, height_str, education_str])
        
        solution_dict = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()