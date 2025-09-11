import itertools
import json

def main():
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    hobbies = ['cooking', 'painting', 'gardening', 'photography']
    animals = ['horse', 'fish', 'cat', 'bird']
    bookgenres = ['fantasy', 'mystery', 'romance', 'science fiction']
    birthdays = ['april', 'jan', 'sept', 'feb']
    musicgenres = ['pop', 'rock', 'classical', 'jazz']

    for name_perm in itertools.permutations(names):
        p_index = name_perm.index('Peter')
        a_index = name_perm.index('Arnold')

        # Generate valid hobby permutations where Arnold's hobby is gardening
        valid_hobbies = []
        for h in itertools.permutations(hobbies):
            if h[a_index] == 'gardening':
                valid_hobbies.append(h)
        
        # Generate valid birthday permutations: Peter's is feb, Arnold's is april
        valid_birthdays = []
        for b in itertools.permutations(birthdays):
            if b[p_index] == 'feb' and b[a_index] == 'april':
                valid_birthdays.append(b)
        
        # Generate valid music permutations: Peter's is pop
        valid_music = []
        for m in itertools.permutations(musicgenres):
            if m[p_index] == 'pop':
                valid_music.append(m)
        
        # Generate valid animal permutations: Peter's is fish
        valid_animals = []
        for a in itertools.permutations(animals):
            if a[p_index] == 'fish':
                valid_animals.append(a)
        
        # Now iterate through all combinations of these
        for h_perm in valid_hobbies:
            for b_perm in valid_birthdays:
                for m_perm in valid_music:
                    for a_perm in valid_animals:
                        # Now generate bookgenres permutations
                        for bg_perm in itertools.permutations(bookgenres):
                            valid = True

                            # Constraint 1: cooking → romance
                            for i in range(4):
                                if h_perm[i] == 'cooking' and bg_perm[i] != 'romance':
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 7: horse → rock
                            for i in range(4):
                                if a_perm[i] == 'horse' and m_perm[i] != 'rock':
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 9: jazz → cooking
                            for i in range(4):
                                if m_perm[i] == 'jazz' and h_perm[i] != 'cooking':
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 10: rock → mystery
                            for i in range(4):
                                if m_perm[i] == 'rock' and bg_perm[i] != 'mystery':
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Constraint 4: romance not in house 4
                            if bg_perm[3] == 'romance':
                                valid = False
                            if not valid:
                                continue

                            # Constraint 11: painting directly left of romance
                            found = False
                            for i in range(3):  # 0,1,2
                                if h_perm[i] == 'painting' and bg_perm[i+1] == 'romance':
                                    found = True
                                    break
                            if not found:
                                valid = False
                            if not valid:
                                continue

                            # Constraint 14: rock directly left of jan
                            rock_index = -1
                            for i in range(4):
                                if m_perm[i] == 'rock':
                                    rock_index = i
                                    break
                            if rock_index != -1:
                                if rock_index + 1 >= 4 or b_perm[rock_index + 1] != 'jan':
                                    valid = False
                            if not valid:
                                continue

                            # Constraint 15: cooking not in house 3 (index 2)
                            if h_perm[2] == 'cooking':
                                valid = False
                            if not valid:
                                continue

                            # Constraint 16: cat to the right of horse
                            horse_index = -1
                            cat_index = -1
                            for i in range(4):
                                if a_perm[i] == 'horse':
                                    horse_index = i
                                if a_perm[i] == 'cat':
                                    cat_index = i
                            if cat_index <= horse_index:
                                valid = False
                            if not valid:
                                continue

                            # Constraint 3: Eric not in house 2 (index 1)
                            if name_perm[1] == 'Eric':
                                valid = False
                            if not valid:
                                continue

                            # Constraint 6: Alice right of fantasy
                            alice_index = name_perm.index('Alice')
                            fantasy_index = -1
                            for i in range(4):
                                if bg_perm[i] == 'fantasy':
                                    fantasy_index = i
                                    break
                            if fantasy_index == -1 or alice_index <= fantasy_index:
                                valid = False
                            if not valid:
                                continue

                            # Check cooking → jazz
                            cooking_index = -1
                            for i in range(4):
                                if h_perm[i] == 'cooking':
                                    cooking_index = i
                                    if m_perm[i] != 'jazz':
                                        valid = False
                            if cooking_index == -1 or not valid:
                                continue

                            # If all constraints are met, build the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                                    "rows": []
                                }
                            }
                            for i in range(4):
                                house_num = str(i+1)
                                name = name_perm[i]
                                hobby = h_perm[i]
                                animal = a_perm[i]
                                bookgenre = bg_perm[i]
                                birthday = b_perm[i]
                                musicgenre = m_perm[i]
                                solution["solution"]["rows"].append([house_num, name, hobby, animal, bookgenre, birthday, musicgenre])

                            # Output as JSON
                            print(json.dumps(solution))
                            return  # exit after first solution

if __name__ == "__main__":
    main()