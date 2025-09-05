from z3 import *
import json

def main():
    # Create Z3 integer variables for each attribute.
    # Each variable represents the house number (1 to 5) for that attribute.
    # Names
    Peter   = Int('Peter')
    Alice   = Int('Alice')
    Eric    = Int('Eric')
    Bob     = Int('Bob')
    Arnold  = Int('Arnold')
    
    # Birthdays
    april   = Int('april')
    feb     = Int('feb')
    mar     = Int('mar')
    jan     = Int('jan')
    sept    = Int('sept')
    
    # Cigars
    pall_mall   = Int('pall_mall')
    prince      = Int('prince')
    dunhill     = Int('dunhill')
    blends      = Int('blends')
    blue_master = Int('blue_master')
    
    # Drinks
    water     = Int('water')
    coffee    = Int('coffee')
    tea       = Int('tea')
    milk      = Int('milk')
    root_beer = Int('root_beer')
    
    s = Solver()
    
    # Domain constraints: every attribute is assigned a house number 1 through 5.
    all_vars = [Peter, Alice, Eric, Bob, Arnold,
                april, feb, mar, jan, sept,
                pall_mall, prince, dunhill, blends, blue_master,
                water, coffee, tea, milk, root_beer]
    for var in all_vars:
        s.add(And(var >= 1, var <= 5))
    
    # Each category must be assigned uniquely.
    s.add(Distinct(Peter, Alice, Eric, Bob, Arnold))
    s.add(Distinct(april, feb, mar, jan, sept))
    s.add(Distinct(pall_mall, prince, dunhill, blends, blue_master))
    s.add(Distinct(water, coffee, tea, milk, root_beer))
    
    # Puzzle Clues:
    # 1. The root beer lover is Eric.
    s.add(root_beer == Eric)
    
    # 2. The person partial to Pall Mall is in the third house.
    s.add(pall_mall == 3)
    
    # 3. The person whose birthday is in April is Bob.
    s.add(april == Bob)
    
    # 4. The Dunhill smoker is the person whose birthday is in March.
    s.add(dunhill == mar)
    
    # 5. Peter is somewhere to the right of the root beer lover.
    s.add(Peter > root_beer)
    
    # 6. There is one house between the person whose birthday is in January and Peter.
    s.add(Abs(Peter - jan) == 2)
    
    # 7. The person who smokes many unique blends is the person whose birthday is in February.
    s.add(blends == feb)
    
    # 8. The person whose birthday is in February is in the second house.
    s.add(feb == 2)
    
    # 9. Arnold is directly left of Peter.
    s.add(Arnold + 1 == Peter)
    
    # 10. The person who likes milk is not in the fifth house.
    s.add(milk != 5)
    
    # 11. The person who smokes Blue Master is the coffee drinker.
    s.add(blue_master == coffee)
    
    # 12. There is one house between the tea drinker and the coffee drinker.
    s.add(Abs(tea - coffee) == 2)
    
    # 13. Eric is in the third house.
    s.add(Eric == 3)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        
        # Build mappings from attribute value to its house number.
        names = {
            "Peter": m[Peter].as_long(),
            "Alice": m[Alice].as_long(),
            "Eric": m[Eric].as_long(),
            "Bob": m[Bob].as_long(),
            "Arnold": m[Arnold].as_long()
        }
        birthdays = {
            "april": m[april].as_long(),
            "feb": m[feb].as_long(),
            "mar": m[mar].as_long(),
            "jan": m[jan].as_long(),
            "sept": m[sept].as_long()
        }
        cigars = {
            "pall mall": m[pall_mall].as_long(),
            "prince": m[prince].as_long(),
            "dunhill": m[dunhill].as_long(),
            "blends": m[blends].as_long(),
            "blue master": m[blue_master].as_long()
        }
        drinks = {
            "water": m[water].as_long(),
            "coffee": m[coffee].as_long(),
            "tea": m[tea].as_long(),
            "milk": m[milk].as_long(),
            "root beer": m[root_beer].as_long()
        }
        
        # Prepare the solution rows by iterating houses 1 to 5.
        solution_rows = []
        for house in range(1, 6):
            house_name = [name for name, pos in names.items() if pos == house][0]
            house_birthday = [bd for bd, pos in birthdays.items() if pos == house][0]
            house_cigar = [cigar for cigar, pos in cigars.items() if pos == house][0]
            house_drink = [drink for drink, pos in drinks.items() if pos == house][0]
            solution_rows.append([str(house), house_name, house_birthday, house_cigar, house_drink])
        
        output = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == '__main__':
    main()