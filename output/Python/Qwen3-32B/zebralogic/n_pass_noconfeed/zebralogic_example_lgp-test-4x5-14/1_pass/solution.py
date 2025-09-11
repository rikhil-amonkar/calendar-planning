import itertools
import json

def main():
    # Define the categories
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    mothers = ['Janelle', 'Holly', 'Aniya', 'Kailyn']
    smoothies = ['watermelon', 'dragonfruit', 'desert', 'cherry']
    heights = ['tall', 'average', 'short', 'very short']
    education = ['high school', 'associate', 'master', 'bachelor']

    # Generate valid permutations for each category
    valid_mothers = [p for p in itertools.permutations(mothers) if p[2] == 'Janelle']
    valid_heights = [p for p in itertools.permutations(heights) if p[2] == 'tall']
    valid_names = [p for p in itertools.permutations(names) if p[2] == 'Alice']
    valid_smoothies = [p for p in itertools.permutations(smoothies) if p[0] != 'desert']
    valid_education = list(itertools.permutations(education))

    # Iterate through all possible combinations
    for m in valid_mothers:
        for h in valid_heights:
            for n in valid_names:
                for s in valid_smoothies:
                    for e in valid_education:
                        # Check all constraints
                        # Clue 2: Desert and master
                        desert_idx = s.index('desert')
                        if e[desert_idx] != 'master':
                            continue
                        # Clue 7: Kailyn's mother has associate
                        kailyn_idx = m.index('Kailyn')
                        if e[kailyn_idx] != 'associate':
                            continue
                        # Clue 8: Cherry's mother is Aniya
                        cherry_idx = s.index('cherry')
                        if m[cherry_idx] != 'Aniya':
                            continue
                        # Clue 4: very short is left of high school
                        vs_idx = h.index('very short')
                        hs_idx = e.index('high school')
                        if vs_idx >= hs_idx:
                            continue
                        # Clue 5: Eric and Cherry adjacent
                        eric_idx = n.index('Eric')
                        if abs(eric_idx - cherry_idx) != 1:
                            continue
                        # Clue 6: high school not in house 3 (index 2)
                        if e[2] == 'high school':
                            continue
                        # Clue 10: Arnold is right of average
                        arnold_idx = n.index('Arnold')
                        avg_idx = h.index('average')
                        if arnold_idx <= avg_idx:
                            continue
                        # Clue 11: Dragonfruit directly left of short
                        dragon_idx = s.index('dragonfruit')
                        if dragon_idx + 1 >= len(h):
                            continue  # if dragonfruit is in last house, no next
                        if h[dragon_idx + 1] != 'short':
                            continue

                        # If all constraints passed, build the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                                "rows": []
                            }
                        }
                        for i in range(4):
                            house_num = str(i + 1)
                            name = n[i]
                            mother = m[i]
                            smoothie = s[i]
                            height = h[i]
                            ed = e[i]
                            solution["solution"]["rows"].append([
                                house_num, name, mother, smoothie, height, ed
                            ])

                        # Output the JSON
                        print(json.dumps(solution, indent=2))
                        return  # Assuming only one solution

if __name__ == "__main__":
    main()