import itertools
import json

def main():
    names = ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter']
    mothers = ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn']
    pets = ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit']
    
    for n in itertools.permutations(names):
        if n[1] == 'Bob':
            continue
            
        alice_index = None
        carol_index = None
        for idx, name in enumerate(n):
            if name == 'Alice':
                alice_index = idx
            if name == 'Carol':
                carol_index = idx
        if alice_index is None or carol_index is None or alice_index + 1 != carol_index:
            continue
            
        arnold_index = n.index('Arnold')
        eric_index = n.index('Eric')
        
        for m in itertools.permutations(mothers):
            if m[carol_index] != 'Aniya':
                continue
            if m[eric_index] != 'Kailyn':
                continue
            if arnold_index < 5:
                if m[arnold_index+1] != 'Holly':
                    continue
            else:
                continue
                
            if m[arnold_index] != 'Janelle':
                continue
                
            for p in itertools.permutations(pets):
                if p[arnold_index] != 'cat':
                    continue
                if p[eric_index] != 'rabbit':
                    continue
                    
                fish_valid = False
                for i in range(6):
                    if p[i] == 'fish':
                        if m[i] == 'Sarah':
                            fish_valid = True
                            break
                if not fish_valid:
                    continue
                    
                if abs(arnold_index - eric_index) != 3:
                    continue
                    
                if eric_index == 0:
                    continue
                if p[eric_index-1] != 'hamster':
                    continue
                    
                dog_index = None
                for i in range(6):
                    if p[i] == 'dog':
                        dog_index = i
                        break
                if dog_index is None:
                    continue
                if abs(dog_index - arnold_index) != 2:
                    continue
                    
                solution_rows = []
                for i in range(6):
                    solution_rows.append([str(i+1), n[i], m[i], p[i]])
                    
                result = {
                    "solution": {
                        "header": ["House", "Name", "The mothers' names", "pet"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(result))
                return
                
    print(json.dumps({"solution": None}))
    
if __name__ == "__main__":
    main()