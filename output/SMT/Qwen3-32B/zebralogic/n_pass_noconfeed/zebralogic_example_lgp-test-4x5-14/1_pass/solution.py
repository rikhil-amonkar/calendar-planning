from z3 import *
import json

# Define EnumSorts for each attribute
Names, (Peter, Alice, Eric, Arnold) = EnumSort('Names', ['Peter', 'Alice', 'Eric', 'Arnold'])
Mothers, (Janelle, Holly, Aniya, Kailyn) = EnumSort('Mothers', ['Janelle', 'Holly', 'Aniya', 'Kailyn'])
Smoothies, (watermelon, dragonfruit, desert, cherry) = EnumSort('Smoothies', ['watermelon', 'dragonfruit', 'desert', 'cherry'])
Heights, (tall, average, short, very_short) = EnumSort('Heights', ['tall', 'average', 'short', 'very_short'])
Educations, (high_school, associate, master, bachelor) = EnumSort('Educations', ['high school', 'associate', 'master', 'bachelor'])

# Create variables for each house
# Names
name_1 = Const('name_1', Names)
name_2 = Const('name_2', Names)
name_3 = Const('name_3', Names)
name_4 = Const('name_4', Names)

# Mothers
mother_1 = Const('mother_1', Mothers)
mother_2 = Const('mother_2', Mothers)
mother_3 = Const('mother_3', Mothers)
mother_4 = Const('mother_4', Mothers)

# Smoothies
smoothie_1 = Const('smoothie_1', Smoothies)
smoothie_2 = Const('smoothie_2', Smoothies)
smoothie_3 = Const('smoothie_3', Smoothies)
smoothie_4 = Const('smoothie_4', Smoothies)

# Heights
height_1 = Const('height_1', Heights)
height_2 = Const('height_2', Heights)
height_3 = Const('height_3', Heights)
height_4 = Const('height_4', Heights)

# Educations
education_1 = Const('education_1', Educations)
education_2 = Const('education_2', Educations)
education_3 = Const('education_3', Educations)
education_4 = Const('education_4', Educations)

s = Solver()

# Add distinct constraints for each attribute
s.add(Distinct(name_1, name_2, name_3, name_4))
s.add(Distinct(mother_1, mother_2, mother_3, mother_4))
s.add(Distinct(smoothie_1, smoothie_2, smoothie_3, smoothie_4))
s.add(Distinct(height_1, height_2, height_3, height_4))
s.add(Distinct(education_1, education_2, education_3, education_4))

# Add clues
s.add(mother_3 == Janelle)  # Clue 1
s.add(height_3 == tall)     # Clue 9
s.add(name_3 == Alice)      # Clue 12

# Clue 2: Desert smoothie lover has master's degree
s.add(Implies(smoothie_1 == desert, education_1 == master))
s.add(Implies(smoothie_2 == desert, education_2 == master))
s.add(Implies(smoothie_3 == desert, education_3 == master))
s.add(Implies(smoothie_4 == desert, education_4 == master))

s.add(smoothie_1 != desert)  # Clue 3
s.add(education_3 != high_school)  # Clue 6

# Clue 7: Mother Kailyn has associate's degree
s.add(Implies(mother_1 == Kailyn, education_1 == associate))
s.add(Implies(mother_2 == Kailyn, education_2 == associate))
s.add(Implies(mother_3 == Kailyn, education_3 == associate))
s.add(Implies(mother_4 == Kailyn, education_4 == associate))

# Clue 8: Cherry smoothie lover's mother is Aniya
s.add(Implies(smoothie_1 == cherry, mother_1 == Aniya))
s.add(Implies(smoothie_2 == cherry, mother_2 == Aniya))
s.add(Implies(smoothie_3 == cherry, mother_3 == Aniya))
s.add(Implies(smoothie_4 == cherry, mother_4 == Aniya))

# Clue 4: very_short is to the left of high school
s.add(Or(
    And(height_1 == very_short, Or(education_2 == high_school, education_3 == high_school, education_4 == high_school)),
    And(height_2 == very_short, Or(education_3 == high_school, education_4 == high_school)),
    And(height_3 == very_short, education_4 == high_school)
))

# Clue 5: Eric and Cherry are adjacent
s.add(Or(
    And(name_1 == Eric, smoothie_2 == cherry),
    And(name_2 == Eric, smoothie_1 == cherry),
    And(name_2 == Eric, smoothie_3 == cherry),
    And(name_3 == Eric, smoothie_2 == cherry),
    And(name_3 == Eric, smoothie_4 == cherry),
    And(name_4 == Eric, smoothie_3 == cherry)
))

# Clue 10: Arnold is to the right of average height
s.add(Or(
    And(name_2 == Arnold, height_1 == average),
    And(name_3 == Arnold, Or(height_1 == average, height_2 == average)),
    And(name_4 == Arnold, Or(height_1 == average, height_2 == average, height_3 == average))
))

# Clue 11: Dragonfruit directly left of short
s.add(Or(
    And(smoothie_1 == dragonfruit, height_2 == short),
    And(smoothie_2 == dragonfruit, height_3 == short),
    And(smoothie_3 == dragonfruit, height_4 == short)
))

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
            "rows": []
        }
    }
    # Extract values for each house
    for house_num in range(1, 5):
        house = str(house_num)
        name = model.eval(globals()[f'name_{house_num}']).decl().name()
        mother = model.eval(globals()[f'mother_{house_num}']).decl().name()
        smoothie = model.eval(globals()[f'smoothie_{house_num}']).decl().name()
        height = model.eval(globals()[f'height_{house_num}']).decl().name()
        education = model.eval(globals()[f'education_{house_num}']).decl().name()
        solution["solution"]["rows"].append([house, name, mother, smoothie, height, education])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")