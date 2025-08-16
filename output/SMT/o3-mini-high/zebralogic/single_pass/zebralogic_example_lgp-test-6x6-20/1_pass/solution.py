from z3 import *
import json

# Create a solver
s = Solver()

# Define domains for each category as integer variables from 1 to 6
# Each variable represents the house number (1 = leftmost, 6 = rightmost)

# Names
names = {
    "Alice": Int("Alice"),
    "Peter": Int("Peter"),
    "Eric": Int("Eric"),
    "Bob": Int("Bob"),
    "Arnold": Int("Arnold"),
    "Carol": Int("Carol")
}

# Cigars
cigars = {
    "pall mall": Int("pall_mall"),
    "yellow monster": Int("yellow_monster"),
    "dunhill": Int("dunhill"),
    "blue master": Int("blue_master"),
    "prince": Int("prince"),
    "blends": Int("blends")  # "smokes many unique blends"
}

# Music Genres
music = {
    "hip hop": Int("hip_hop"),
    "jazz": Int("jazz"),
    "country": Int("country"),
    "pop": Int("pop"),
    "classical": Int("classical"),
    "rock": Int("rock")
}

# Drinks
drinks = {
    "water": Int("water"),
    "milk": Int("milk"),
    "boba tea": Int("boba_tea"),
    "tea": Int("tea"),
    "root beer": Int("root_beer"),
    "coffee": Int("coffee")
}

# Mothers
mothers = {
    "Kailyn": Int("Kailyn"),
    "Penny": Int("Penny"),
    "Janelle": Int("Janelle"),
    "Holly": Int("Holly"),
    "Sarah": Int("Sarah"),
    "Aniya": Int("Aniya")
}

# Lunch/Foods
foods = {
    "soup": Int("soup"),
    "pizza": Int("pizza"),
    "spaghetti": Int("spaghetti"),
    "stir fry": Int("stir_fry"),
    "stew": Int("stew"),
    "grilled cheese": Int("grilled_cheese")
}

# Make sure each variable is between 1 and 6
def add_range_constraints(category):
    for key in category:
        s.add(And(category[key] >= 1, category[key] <= 6))

for cat in [names, cigars, music, drinks, mothers, foods]:
    add_range_constraints(cat)

# Each category must have all different house numbers
s.add(Distinct(list(names.values())))
s.add(Distinct(list(cigars.values())))
s.add(Distinct(list(music.values())))
s.add(Distinct(list(drinks.values())))
s.add(Distinct(list(mothers.values())))
s.add(Distinct(list(foods.values())))

# Now add the clues as constraints:

# 1. Carol is directly left of the person who loves eating grilled cheese.
s.add(names["Carol"] + 1 == foods["grilled cheese"])

# 2. Eric is not in the second house.
s.add(names["Eric"] != 2)

# 3. The person whose mother's name is Holly is somewhere to the right of Carol.
s.add(mothers["Holly"] > names["Carol"])

# 4. The person who loves eating grilled cheese is somewhere to the right of the person who loves rock music.
s.add(foods["grilled cheese"] > music["rock"])

# 5. Eric is directly left of Carol.
s.add(names["Eric"] + 1 == names["Carol"])

# 6. The person who loves pop music is not in the third house.
s.add(music["pop"] != 3)

# 7. Eric is the person who loves country music.
s.add(names["Eric"] == music["country"])

# 8. The person who loves classical music is in the sixth house.
s.add(music["classical"] == 6)

# 9. The coffee drinker is Bob.
s.add(names["Bob"] == drinks["coffee"])

# 10. The person who smokes many unique blends is Peter.
s.add(names["Peter"] == cigars["blends"])

# 11. The person who loves the stew is not in the fifth house.
s.add(foods["stew"] != 5)

# 12. The root beer lover is directly left of the person whose mother's name is Janelle.
s.add(drinks["root beer"] + 1 == mothers["Janelle"])

# 13. There are two houses between the person whose mother's name is Sarah and the person who smokes Yellow Monster.
s.add(Or(mothers["Sarah"] + 3 == cigars["yellow monster"], cigars["yellow monster"] + 3 == mothers["Sarah"]))

# 14. Eric is the tea drinker.
s.add(drinks["tea"] == names["Eric"])

# 15. The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
s.add(cigars["pall mall"] > foods["stir fry"])

# 16. The person who loves the soup is Bob.
s.add(names["Bob"] == foods["soup"])

# 17. The person who loves hip-hop music is directly left of the person whose mother's name is Kailyn.
s.add(music["hip hop"] + 1 == mothers["Kailyn"])

# 18. Arnold is somewhere to the right of the person whose mother's name is Kailyn.
s.add(names["Arnold"] > mothers["Kailyn"])

# 19. The one who only drinks water is directly left of the person who smokes Blue Master.
s.add(drinks["water"] + 1 == cigars["blue master"])

# 20. The person who loves the spaghetti eater is somewhere to the left of the person who smokes many unique blends.
# (Interpreted: The person who loves spaghetti is somewhere to the left of the person (Peter) who smokes blends.)
s.add(foods["spaghetti"] < names["Peter"])

# 21. The person whose mother's name is Sarah is directly left of the person who loves jazz music.
s.add(mothers["Sarah"] + 1 == music["jazz"])

# 22. The person who loves hip-hop music is directly left of the root beer lover.
s.add(music["hip hop"] + 1 == drinks["root beer"])

# 23. The one who only drinks water is the person who loves the stew.
s.add(drinks["water"] == foods["stew"])

# 24. The Dunhill smoker is not in the second house.
s.add(cigars["dunhill"] != 2)

# 25. The person who likes milk is the person whose mother's name is Janelle.
s.add(drinks["milk"] == mothers["Janelle"])

# 26. Eric is the person whose mother's name is Aniya.
s.add(names["Eric"] == mothers["Aniya"])

# Check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    
    # For each house from 1 to 6, determine which attribute belongs there.
    def get_item(category, pos):
        for key in category:
            if m.evaluate(category[key]) == pos:
                return key
        return None

    rows = []
    header = ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"]
    for i in range(1, 7):
        row = [
            str(i),
            get_item(names, i),
            get_item(cigars, i),
            get_item(music, i),
            get_item(drinks, i),
            get_item(mothers, i),
            get_item(foods, i)
        ]
        rows.append(row)
        
    result = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")