from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5, 6]

# Define the attributes
names = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
cigars = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
music_genres = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
drinks = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
mothers = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
foods = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]

# Create dictionaries to hold the variables for each attribute
name = {h: String(f"name_{h}") for h in houses}
cigar = {h: String(f"cigar_{h}") for h in houses}
music = {h: String(f"music_{h}") for h in houses}
drink = {h: String(f"drink_{h}") for h in houses}
mother = {h: String(f"mother_{h}") for h in houses}
food = {h: String(f"food_{h}") for h in houses}

# Add constraints that each attribute is unique per house
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([cigar[h] for h in houses]))
s.add(Distinct([music[h] for h in houses]))
s.add(Distinct([drink[h] for h in houses]))
s.add(Distinct([mother[h] for h in houses]))
s.add(Distinct([food[h] for h in houses]))

# Each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([cigar[h] == c for c in cigars]))
    s.add(Or([music[h] == m for m in music_genres]))
    s.add(Or([drink[h] == d for d in drinks]))
    s.add(Or([mother[h] == m for m in mothers]))
    s.add(Or([food[h] == f for f in foods]))

# Add the clues as constraints
# Clue 2: Eric is not in the second house.
s.add(name[2] != "Eric")

# Clue 5: Eric is directly left of Carol.
for h in range(1, 6):
    s.add(Implies(name[h] == "Eric", name[h+1] == "Carol"))

# Clue 1: Carol is directly left of the person who loves eating grilled cheese.
for h in range(1, 6):
    s.add(Implies(name[h] == "Carol", food[h+1] == "grilled cheese"))

# Clue 3: The person whose mother's name is Holly is somewhere to the right of Carol.
# Carol must be in a house with index less than the house with mother Holly
holly_house = Int("holly_house")
s.add(holly_house >= 1, holly_house <= 6)
carol_house = Int("carol_house")
s.add(carol_house >= 1, carol_house <= 6)
for h in houses:
    s.add(Implies(name[h] == "Carol", carol_house == h))
    s.add(Implies(mother[h] == "Holly", holly_house == h))
s.add(holly_house > carol_house)

# Clue 4: The person who loves grilled cheese is somewhere to the right of the person who loves rock music.
grilled_cheese_house = Int("grilled_cheese_house")
rock_house = Int("rock_house")
s.add(grilled_cheese_house >= 1, grilled_cheese_house <= 6)
s.add(rock_house >= 1, rock_house <= 6)
for h in houses:
    s.add(Implies(food[h] == "grilled cheese", grilled_cheese_house == h))
    s.add(Implies(music[h] == "rock", rock_house == h))
s.add(grilled_cheese_house > rock_house)

# Clue 6: The person who loves pop music is not in the third house.
s.add(music[3] != "pop")

# Clue 7: Eric is the person who loves country music.
for h in houses:
    s.add(Implies(name[h] == "Eric", music[h] == "country"))

# Clue 8: The person who loves classical music is in the sixth house.
s.add(music[6] == "classical")

# Clue 9: The coffee drinker is Bob.
for h in houses:
    s.add(Implies(name[h] == "Bob", drink[h] == "coffee"))

# Clue 10: The person who smokes many unique blends is Peter.
for h in houses:
    s.add(Implies(name[h] == "Peter", cigar[h] == "blends"))

# Clue 11: The person who loves the stew is not in the fifth house.
s.add(food[5] != "stew")

# Clue 12: The root beer lover is directly left of the person whose mother's name is Janelle.
for h in range(1, 6):
    s.add(Implies(drink[h] == "root beer", mother[h+1] == "Janelle"))

# Clue 13: There are two houses between the person whose mother's name is Sarah and the person who smokes Yellow Monster.
sarah_house = Int("sarah_house")
yellow_monster_house = Int("yellow_monster_house")
s.add(sarah_house >= 1, sarah_house <= 6)
s.add(yellow_monster_house >= 1, yellow_monster_house <= 6)
for h in houses:
    s.add(Implies(mother[h] == "Sarah", sarah_house == h))
    s.add(Implies(cigar[h] == "yellow monster", yellow_monster_house == h))
s.add(yellow_monster_house == sarah_house + 3)

# Clue 14: Eric is the tea drinker.
for h in houses:
    s.add(Implies(name[h] == "Eric", drink[h] == "tea"))

# Clue 15: The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
pall_mall_house = Int("pall_mall_house")
stir_fry_house = Int("stir_fry_house")
s.add(pall_mall_house >= 1, pall_mall_house <= 6)
s.add(stir_fry_house >= 1, stir_fry_house <= 6)
for h in houses:
    s.add(Implies(cigar[h] == "pall mall", pall_mall_house == h))
    s.add(Implies(food[h] == "stir fry", stir_fry_house == h))
s.add(pall_mall_house > stir_fry_house)

# Clue 16: The person who loves the soup is Bob.
for h in houses:
    s.add(Implies(name[h] == "Bob", food[h] == "soup"))

# Clue 17: The person who loves hip-hop music is directly left of the person whose mother's name is Kailyn.
for h in range(1, 6):
    s.add(Implies(music[h] == "hip hop", mother[h+1] == "Kailyn"))

# Clue 18: Arnold is somewhere to the right of the person whose mother's name is Kailyn.
kailyn_house = Int("kailyn_house")
arnold_house = Int("arnold_house")
s.add(kailyn_house >= 1, kailyn_house <= 6)
s.add(arnold_house >= 1, arnold_house <= 6)
for h in houses:
    s.add(Implies(mother[h] == "Kailyn", kailyn_house == h))
    s.add(Implies(name[h] == "Arnold", arnold_house == h))
s.add(arnold_house > kailyn_house)

# Clue 19: The one who only drinks water is directly left of the person who smokes Blue Master.
for h in range(1, 6):
    s.add(Implies(drink[h] == "water", cigar[h+1] == "blue master"))

# Clue 20: The person who loves the spaghetti eater is somewhere to the left of the person who smokes many unique blends.
spaghetti_house = Int("spaghetti_house")
blends_house = Int("blends_house")
s.add(spaghetti_house >= 1, spaghetti_house <= 6)
s.add(blends_house >= 1, blends_house <= 6)
for h in houses:
    s.add(Implies(food[h] == "spaghetti", spaghetti_house == h))
    s.add(Implies(cigar[h] == "blends", blends_house == h))
s.add(spaghetti_house < blends_house)

# Clue 21: The person whose mother's name is Sarah is directly left of the person who loves jazz music.
for h in range(1, 6):
    s.add(Implies(mother[h] == "Sarah", music[h+1] == "jazz"))

# Clue 22: The person who loves hip-hop music is directly left of the root beer lover.
for h in range(1, 6):
    s.add(Implies(music[h] == "hip hop", drink[h+1] == "root beer"))

# Clue 23: The one who only drinks water is the person who loves the stew.
for h in houses:
    s.add(Implies(drink[h] == "water", food[h] == "stew"))

# Clue 24: The Dunhill smoker is not in the second house.
s.add(cigar[2] != "dunhill")

# Clue 25: The person who likes milk is the person whose mother's name is Janelle.
for h in houses:
    s.add(Implies(drink[h] == "milk", mother[h] == "Janelle"))

# Clue 26: Eric is the person whose mother's name is Aniya.
for h in houses:
    s.add(Implies(name[h] == "Eric", mother[h] == "Aniya"))

# Check if the solver can find a solution
if s.check() == sat:
    m = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            str(m.eval(name[h])),
            str(m.eval(cigar[h])),
            str(m.eval(music[h])),
            str(m.eval(drink[h])),
            str(m.eval(mother[h])),
            str(m.eval(food[h]))
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")