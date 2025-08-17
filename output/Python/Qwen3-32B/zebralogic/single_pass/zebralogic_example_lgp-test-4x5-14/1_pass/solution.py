import itertools
import json

def main():
    # Define the categories
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    mothers = ['Janelle', 'Holly', 'Aniya', 'Kailyn']
    smoothies = ['watermelon', 'dragonfruit', 'desert', 'cherry']
    heights = ['tall', 'average', 'short', 'very short']
    educations = ['high school', 'associate', 'master', 'bachelor']
    
    # Generate valid permutations for Mother, Name, Height
    valid_mother_perms = [p for p in itertools.permutations(mothers) if p[2] == 'Janelle']
    valid_name_perms = [p for p in itertools.permutations(names) if p[2] == 'Alice']
    valid_height_perms = [p for p in itertools.permutations(heights) if p[2] == 'tall']
    
    # Generate all permutations for smoothie and education
    smoothie_perms = list(itertools.permutations(smoothies))
    education_perms = list(itertools.permutations(educations))
    
    # Iterate through all combinations
    for m_perm in valid_mother_perms:
        for n_perm in valid_name_perms:
            for h_perm in valid_height_perms:
                for s_perm in smoothie_perms:
                    for e_perm in education_perms:
                        if check_constraints(m_perm, n_perm, h_perm, s_perm, e_perm):
                            solution = build_solution(n_perm, m_perm, s_perm, h_perm, e_perm)
                            print(json.dumps(solution))
                            return
    
def check_constraints(mother_perm, name_perm, height_perm, smoothie_perm, education_perm):
    # Clue 2: Desert → master
    for i in range(4):
        if smoothie_perm[i] == 'desert' and education_perm[i] != 'master':
            return False
    
    # Clue 3: Desert not in first house
    if smoothie_perm[0] == 'desert':
        return False
    
    # Clue 4: very short is left of high school
    i_vs = None
    j_hs = None
    for i in range(4):
        if height_perm[i] == 'very short':
            i_vs = i
        if education_perm[i] == 'high school':
            j_hs = i
    if i_vs is None or j_hs is None or not (i_vs < j_hs):
        return False
    
    # Clue 5: Eric and Cherry are next to each other
    i_eric = None
    for i in range(4):
        if name_perm[i] == 'Eric':
            i_eric = i
            break
    i_cherry = None
    for i in range(4):
        if smoothie_perm[i] == 'cherry':
            i_cherry = i
            break
    if i_eric is None or i_cherry is None or abs(i_eric - i_cherry) != 1:
        return False
    
    # Clue 6: high school not in third house
    if education_perm[2] == 'high school':
        return False
    
    # Clue 7: Kailyn → associate
    for i in range(4):
        if mother_perm[i] == 'Kailyn' and education_perm[i] != 'associate':
            return False
    
    # Clue 8: Cherry → mother Aniya
    for i in range(4):
        if smoothie_perm[i] == 'cherry' and mother_perm[i] != 'Aniya':
            return False
    
    # Clue 10: Arnold is to the right of average height
    i_arnold = None
    for i in range(4):
        if name_perm[i] == 'Arnold':
            i_arnold = i
            break
    i_avg = None
    for i in range(4):
        if height_perm[i] == 'average':
            i_avg = i
            break
    if i_arnold is None or i_avg is None or not (i_arnold > i_avg):
        return False
    
    # Clue 11: Dragonfruit directly left of short
    for i in range(4):
        if smoothie_perm[i] == 'dragonfruit':
            if i + 1 >= 4 or height_perm[i + 1] != 'short':
                return False
            break  # Only one dragonfruit, so break after checking
    
    # All constraints passed
    return True

def build_solution(name_perm, mother_perm, smoothie_perm, height_perm, education_perm):
    header = ["House", "Name", "Mother", "Smoothie", "Height", "Education"]
    rows = []
    for i in range(4):
        house_num = i + 1
        row = [
            str(house_num),
            name_perm[i],
            mother_perm[i],
            smoothie_perm[i],
            height_perm[i],
            education_perm[i]
        ]
        rows.append(row)
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    main()