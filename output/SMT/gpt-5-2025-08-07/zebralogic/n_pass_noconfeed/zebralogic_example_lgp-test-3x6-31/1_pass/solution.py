import json
from z3 import Int, Solver, Distinct, And, Or, sat

def main():
    # Houses are numbered 1..3 (left to right)
    HOUSES = range(1, 4)

    # Define variables: each attribute value maps to a house number (1..3)
    Eric = Int('Eric')
    Peter = Int('Peter')
    Arnold = Int('Arnold')

    milk = Int('milk')
    water = Int('water')
    tea = Int('tea')

    mountain = Int('mountain')
    city = Int('city')
    beach = Int('beach')

    colonial = Int('colonial')
    victorian = Int('victorian')
    ranch = Int('ranch')

    cat = Int('cat')
    bird = Int('bird')
    horse = Int('horse')

    jan = Int('jan')
    sept = Int('sept')
    april = Int('april')

    all_vars = [
        Eric, Peter, Arnold,
        milk, water, tea,
        mountain, city, beach,
        colonial, victorian, ranch,
        cat, bird, horse,
        jan, sept, april
    ]

    s = Solver()

    # Domain constraints: all variables in 1..3
    for v in all_vars:
        s.add(And(v >= 1, v <= 3))

    # Uniqueness within each category
    s.add(Distinct(Eric, Peter, Arnold))
    s.add(Distinct(milk, water, tea))
    s.add(Distinct(mountain, city, beach))
    s.add(Distinct(colonial, victorian, ranch))
    s.add(Distinct(cat, bird, horse))
    s.add(Distinct(jan, sept, april))

    # Clues:
    # 1. Colonial is somewhere to the left of milk.
    s.add(colonial < milk)

    # 2. City is directly left of Victorian.
    s.add(city + 1 == victorian)

    # 3. January is directly left of Cat.
    s.add(jan + 1 == cat)

    # 4. Water drinker is the Mountain vacationer.
    s.add(water == mountain)

    # 5. The person who keeps horses is Peter.
    s.add(horse == Peter)

    # 6. Victorian is somewhere to the right of Beach vacationer.
    s.add(victorian > beach)

    # 7. Peter prefers City.
    s.add(Peter == city)

    # 8. Mountain vacationer has April birthday.
    s.add(mountain == april)

    # 9. Eric drinks Water.
    s.add(Eric == water)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build mappings for reconstruction
    names = {'Eric': Eric, 'Peter': Peter, 'Arnold': Arnold}
    drinks = {'milk': milk, 'water': water, 'tea': tea}
    vacations = {'mountain': mountain, 'city': city, 'beach': beach}
    house_styles = {'colonial': colonial, 'victorian': victorian, 'ranch': ranch}
    animals = {'cat': cat, 'bird': bird, 'horse': horse}
    birthdays = {'jan': jan, 'sept': sept, 'april': april}

    def attr_at_house(attr_map, house_num):
        for k, v in attr_map.items():
            if m[v].as_long() == house_num:
                return k
        return None

    rows = []
    for h in HOUSES:
        rows.append([
            str(h),
            attr_at_house(names, h),
            attr_at_house(drinks, h),
            attr_at_house(vacations, h),
            attr_at_house(house_styles, h),
            attr_at_house(animals, h),
            attr_at_house(birthdays, h),
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()