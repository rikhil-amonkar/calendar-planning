import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]

    Names = ['Arnold', 'Peter', 'Eric']
    Occupations = ['doctor', 'teacher', 'engineer']
    Educations = ['associate', 'high school', 'bachelor']
    Smoothies = ['desert', 'cherry', 'watermelon']
    Hobbies = ['gardening', 'cooking', 'photography']

    solutions = []

    for names in itertools.permutations(Names):
        # 2. Arnold is not in the third house.
        if names[2] == 'Arnold':
            continue
        # 5. The person who loves cooking is Peter. -> Peter is in house 2 (since cooking is in house 2 from clue 4)
        if names[1] != 'Peter':
            continue

        for hobbies in itertools.permutations(Hobbies):
            # 4. The person who loves cooking is in the second house.
            if hobbies[1] != 'cooking':
                continue

            for occupations in itertools.permutations(Occupations):
                # 8. The person who loves cooking is the person who is a doctor. -> house 2 is doctor
                if occupations[1] != 'doctor':
                    continue
                # 9. The photography enthusiast is the person who is a teacher.
                if occupations[hobbies.index('photography')] != 'teacher':
                    continue

                for smoothies in itertools.permutations(Smoothies):
                    # 1. The Desert smoothie lover is the person who is a doctor. -> house of doctor (2) drinks desert
                    if smoothies[1] != 'desert':
                        continue
                    # 3. Cherry is somewhere to the right of Peter (Peter is in house 2) -> Cherry in house 3
                    if smoothies.index('cherry') <= 1:
                        continue

                    for educations in itertools.permutations(Educations):
                        # 7. Bachelor's is somewhere to the right of the Desert smoothie lover (doctor at house 2) -> Bachelor's in house 3
                        if educations.index('bachelor') <= 1:
                            continue
                        # 6. Associate's degree is somewhere to the right of the person who enjoys gardening.
                        if educations.index('associate') <= hobbies.index('gardening'):
                            continue

                        # All constraints satisfied; record solution
                        rows = []
                        for i in range(3):
                            row = [
                                str(i + 1),
                                names[i],
                                occupations[i],
                                educations[i],
                                smoothies[i],
                                hobbies[i]
                            ]
                            rows.append(row)
                        solutions.append(rows)

    # Prefer unique solution; if multiple, take the first
    if not solutions:
        raise RuntimeError("No solution found.")
    final_rows = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
            "rows": final_rows
        }
    }
    return result

if __name__ == "__main__":
    print(json.dumps(solve_puzzle(), ensure_ascii=False))