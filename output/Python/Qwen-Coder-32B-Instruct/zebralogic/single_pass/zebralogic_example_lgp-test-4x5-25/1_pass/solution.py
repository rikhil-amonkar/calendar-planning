import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Arnold", "Peter", "Eric", "Alice"]
    house_styles = ["craftsman", "colonial", "victorian", "ranch"]
    hair_colors = ["red", "blonde", "black", "brown"]
    children = ["Bella", "Fred", "Meredith", "Samantha"]
    book_genres = ["mystery", "fantasy", "romance", "science fiction"]

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(house_styles)) * \
                       list(itertools.permutations(hair_colors)) * \
                       list(itertools.permutations(children)) * \
                       list(itertools.permutations(book_genres))

    # Define the constraints
    def constraint1(permutation):
        return permutation[1][2] == "craftsman"

    def constraint2(permutation):
        return permutation[0].index("Alice") == permutation[4].index("romance")

    def constraint3(permutation):
        return permutation[2][3] == "brown"

    def constraint4(permutation):
        return permutation[3][3] == "Samantha"

    def constraint5(permutation):
        red_hair_index = permutation[2].index("red")
        ranch_house_index = permutation[1].index("ranch")
        return red_hair_index < ranch_house_index

    def constraint6(permutation):
        return permutation[3][0] == "Bella"

    def constraint7(permutation):
        return permutation[2][0] == "red"

    def constraint8(permutation):
        return permutation[0].index("Alice") == permutation[1].index("colonial")

    def constraint9(permutation):
        return permutation[2][1] == "black"

    def constraint10(permutation):
        return permutation[0].index("Peter") == permutation[4].index("fantasy")

    def constraint11(permutation):
        return permutation[3][0] == "Meredith"

    def constraint12(permutation):
        return permutation[2][1] == "black"

    def constraint13(permutation):
        return permutation[0].index("Arnold") == permutation[4].index("science fiction")

    # Check all permutations against the constraints
    for permutation in itertools.product(all_permutations, repeat=1):
        if (constraint1(permutation) and constraint2(permutation) and constraint3(permutation) and
            constraint4(permutation) and constraint5(permutation) and constraint6(permutation) and
            constraint7(permutation) and constraint8(permutation) and constraint9(permutation) and
            constraint10(permutation) and constraint11(permutation) and constraint12(permutation) and
            constraint13(permutation)):
            solution = {
                "solution": {
                    "header": ["House", "Name", "House Style", "Hair Color", "Child", "Favorite Book Genre"],
                    "rows": []
                }
            }
            for i in range(4):
                solution["solution"]["rows"].append([
                    str(i + 1),
                    permutation[0][i],
                    permutation[1][i],
                    permutation[2][i],
                    permutation[3][i],
                    permutation[4][i]
                ])
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())