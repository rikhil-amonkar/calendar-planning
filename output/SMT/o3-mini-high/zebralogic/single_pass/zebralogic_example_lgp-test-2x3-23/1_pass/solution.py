from z3 import *
import json

def main():
    # Define enumeration sorts for the different attributes.
    Name = Datatype('Name')
    Name.declare('Eric')
    Name.declare('Arnold')
    Name = Name.create()

    Child = Datatype('Child')
    Child.declare('Bella')
    Child.declare('Fred')
    Child = Child.create()

    Food = Datatype('Food')
    Food.declare('grilled_cheese')
    Food.declare('pizza')
    Food = Food.create()

    houses = 2
    # Create variables for each house's attributes.
    house_names = [Const(f"name_{i}", Name) for i in range(houses)]
    house_children = [Const(f"child_{i}", Child) for i in range(houses)]
    house_food = [Const(f"food_{i}", Food) for i in range(houses)]
    
    s = Solver()

    # Each attribute across houses must be unique.
    s.add(Distinct(house_names))
    s.add(Distinct(house_children))
    s.add(Distinct(house_food))

    # Clue 1: "The person who is a pizza lover is Arnold."
    # For any house that has Food 'pizza', the Name must be Arnold.
    for i in range(houses):
        s.add(Implies(house_food[i] == Food.pizza, house_names[i] == Name.Arnold))

    # Clue 2: "The person who loves eating grilled cheese is directly left of the person's child is named Fred."
    # With houses numbered 1 (left) and 2 (right), this forces:
    # House 1 must have grilled cheese and house 2 must have child Fred.
    s.add(house_food[0] == Food.grilled_cheese)
    s.add(house_children[1] == Child.Fred)

    # Given the distinctness and the fact that there are only two houses,
    # House 2 cannot have grilled cheese (because House 1 already has it), so House 2 must have pizza.
    # That in turn forces House 2's name to be Arnold (by Clue 1),
    # and by distinctness, House 1's name is then Eric.
    s.add(house_food[1] == Food.pizza)

    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(houses):
            # House numbers are 1-indexed.
            house_number = str(i + 1)
            # Extract names and child names from the model.
            name_val = m.evaluate(house_names[i])
            child_val = m.evaluate(house_children[i])
            food_val = m.evaluate(house_food[i])
            
            # Convert the Z3 enum values to strings.
            name_str = str(name_val)
            child_str = str(child_val)
            # For food, preserve the original string formatting for "grilled cheese"
            food_str = "grilled cheese" if str(food_val) == "grilled_cheese" else "pizza"
            
            rows.append([house_number, name_str, child_str, food_str])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Children", "Food"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()