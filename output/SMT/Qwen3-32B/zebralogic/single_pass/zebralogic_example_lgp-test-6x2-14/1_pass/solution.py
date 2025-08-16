from z3 import *
import json

def main():
    s = Solver()

    # Define names and cigars
    names = ['Carol', 'Peter', 'Eric', 'Arnold', 'Alice', 'Bob']
    cigars = ['blends', 'yellow monster', 'pall mall', 'blue master', 'dunhill', 'prince']

    # Create variables for each house's name and cigar (0-based index for houses 1-6)
    name = [Int(f'name_{i+1}') for i in range(6)]
    cigar = [Int(f'cigar_{i+1}') for i in range(6)]

    # Constraints: all names and cigars are distinct and in range
    for i in range(6):
        s.add(And(0 <= name[i], name[i] < 6))
        s.add(And(0 <= cigar[i], cigar[i] < 6))
    s.add(Distinct(name))
    s.add(Distinct(cigar))

    # Clue 2: Blue Master is in house 5 (index 4)
    s.add(cigar[4] == 3)  # blue master is index 3 in cigars list

    # Clue 5: Pall Mall is in house 3 (index 2)
    s.add(cigar[2] == 2)  # pall mall is index 2

    # Clue 6: Eric is in house 6 (index 5)
    s.add(name[5] == 2)  # Eric is index 2 in names

    # Clue 8: Peter is in house 1 (index 0)
    s.add(name[0] == 1)  # Peter is index 1

    # Clue 9: Bob is in house 3 (index 2)
    s.add(name[2] == 5)  # Bob is index 5

    # Clue 7: Carol and Eric are next to each other. Since Eric is in house 6, Carol must be in house 5.
    s.add(name[4] == 0)  # Carol is index 0 in house 5 (index 4)

    # Now, add other constraints.

    # Clue 1: Arnold is left of blends.
    # Find positions of Arnold and blends.
    pos_arnold = Sum([If(name[i] == 3, i, 0) for i in range(6)])  # Arnold is index 3 in names
    pos_blends = Sum([If(cigar[i] == 0, i, 0) for i in range(6)])  # blends is index 0
    s.add(pos_arnold < pos_blends)

    # Clue 3: Arnold is left of Prince.
    pos_prince = Sum([If(cigar[i] == 5, i, 0) for i in range(6)])  # prince is index 5
    s.add(pos_arnold < pos_prince)

    # Clue 4: one house between Yellow Monster and blends.
    pos_yellow_monster = Sum([If(cigar[i] == 1, i, 0) for i in range(6)])  # yellow monster is index 1
    s.add(Or(pos_yellow_monster - pos_blends == 2, pos_blends - pos_yellow_monster == 2))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar"],
                "rows": []
            }
        }
        for i in range(6):
            house_num = i + 1
            n = names[model[name[i]].as_long()]
            c = cigars[model[cigar[i]].as_long()]
            solution["solution"]["rows"].append([str(house_num), n, c])
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()