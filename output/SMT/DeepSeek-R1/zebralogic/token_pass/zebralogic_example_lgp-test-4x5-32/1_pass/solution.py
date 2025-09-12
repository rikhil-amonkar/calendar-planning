from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Define enums for each category
    Name, (Arnold, Alice, Eric, Peter) = EnumSort('Name', ['Arnold', 'Alice', 'Eric', 'Peter'])
    Hobby, (cooking, painting, photography, gardening) = EnumSort('Hobby', ['cooking', 'painting', 'photography', 'gardening'])
    Birthday, (april, jan, sept, feb) = EnumSort('Birthday', ['april', 'jan', 'sept', 'feb'])
    Education, (master, bachelor, associate, high_school) = EnumSort('Education', ['master', 'bachelor', 'associate', 'high school'])
    Smoothie, (cherry, watermelon, desert, dragonfruit) = EnumSort('Smoothie', ['cherry', 'watermelon', 'desert', 'dragonfruit'])
    
    # Create variables for each house
    houses = [1, 2, 3, 4]
    names = [Const(f'n_{i}', Name) for i in houses]
    hobbies = [Const(f'h_{i}', Hobby) for i in houses]
    birthdays = [Const(f'b_{i}', Birthday) for i in houses]
    educations = [Const(f'e_{i}', Education) for i in houses]
    smoothies = [Const(f's_{i}', Smoothie) for i in houses]
    
    # Add uniqueness constraints
    s.add(Distinct(names))
    s.add(Distinct(hobbies))
    s.add(Distinct(birthdays))
    s.add(Distinct(educations))
    s.add(Distinct(smoothies))
    
    # Clue 1: Desert smoothie lover has January birthday
    for i in range(4):
        s.add(Implies(smoothies[i] == desert, birthdays[i] == jan))
    
    # Clue 2: Eric has bachelor's degree
    for i in range(4):
        s.add(Implies(names[i] == Eric, educations[i] == bachelor))
    
    # Clue 3: January birthday has bachelor's degree
    for i in range(4):
        s.add(Implies(birthdays[i] == jan, educations[i] == bachelor))
    
    # Clue 4: High school diploma in third house
    s.add(educations[2] == high_school)
    
    # Clue 5: Watermelon smoothie not in third house
    s.add(smoothies[2] != watermelon)
    
    # Clue 6: Arnold has associate's degree
    for i in range(4):
        s.add(Implies(names[i] == Arnold, educations[i] == associate))
    
    # Clue 7: Master's degree means painting hobby
    for i in range(4):
        s.add(Implies(educations[i] == master, hobbies[i] == painting))
    
    # Clue 8: One house between Dragonfruit and September birthday
    dragonfruit_house = Int('dragonfruit_house')
    sept_house = Int('sept_house')
    s.add(dragonfruit_house >= 1, dragonfruit_house <= 4)
    s.add(sept_house >= 1, sept_house <= 4)
    for i in range(4):
        s.add(Implies(smoothies[i] == dragonfruit, dragonfruit_house == i+1))
        s.add(Implies(birthdays[i] == sept, sept_house == i+1))
    s.add(Or(
        dragonfruit_house - sept_house == 2,
        dragonfruit_house - sept_house == -2
    ))
    
    # Clue 9: High school diploma means September birthday
    for i in range(4):
        s.add(Implies(educations[i] == high_school, birthdays[i] == sept))
    
    # Clue 10: Cooking hobby is Alice
    for i in range(4):
        s.add(Implies(hobbies[i] == cooking, names[i] == Alice))
    
    # Clue 11: April birthday and gardening hobby are adjacent
    april_house = Int('april_house')
    gardening_house = Int('gardening_house')
    s.add(april_house >= 1, april_house <= 4)
    s.add(gardening_house >= 1, gardening_house <= 4)
    for i in range(4):
        s.add(Implies(birthdays[i] == april, april_house == i+1))
        s.add(Implies(hobbies[i] == gardening, gardening_house == i+1))
    s.add(Or(
        april_house - gardening_house == 1,
        april_house - gardening_house == -1
    ))
    
    # Clue 12: Painting hobby means February birthday
    for i in range(4):
        s.add(Implies(hobbies[i] == painting, birthdays[i] == feb))
    
    # Check solution
    if s.check() == sat:
        m = s.model()
        solution = []
        for i in range(4):
            house = i + 1
            name_val = m.eval(names[i])
            hobby_val = m.eval(hobbies[i])
            birthday_val = m.eval(birthdays[i])
            education_val = m.eval(educations[i])
            smoothie_val = m.eval(smoothies[i])
            
            # Convert to string values
            row = [
                str(house),
                str(name_val),
                str(hobby_val),
                str(birthday_val),
                str(education_val),
                str(smoothie_val)
            ]
            solution.append(row)
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                "rows": solution
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()