import itertools
import json

def main():
    names = ['Eric', 'Peter', 'Arnold']
    mothers = ['Holly', 'Aniya', 'Janelle']
    lunches = ['pizza', 'grilled cheese', 'spaghetti']
    
    found = False
    solution = None
    
    for n_perm in itertools.permutations(names):
        for m_perm in itertools.permutations(mothers):
            for l_perm in itertools.permutations(lunches):
                # Check constraint 3: grilled cheese eater is Eric
                grill_index = None
                for i in range(3):
                    if l_perm[i] == 'grilled cheese':
                        grill_index = i
                        break
                if grill_index is None:
                    continue
                if n_perm[grill_index] != 'Eric':
                    continue
                
                # Check constraint 4: Peter has mother Holly
                peter_index = None
                for i in range(3):
                    if n_perm[i] == 'Peter':
                        peter_index = i
                        break
                if peter_index is None:
                    continue
                if m_perm[peter_index] != 'Holly':
                    continue
                
                # Check constraint 2: grilled cheese directly left of mother Aniya
                if grill_index == 2:
                    continue
                if m_perm[grill_index+1] != 'Aniya':
                    continue
                
                # Check constraint 1: spaghetti eater and Peter are adjacent
                spaghetti_index = None
                for i in range(3):
                    if l_perm[i] == 'spaghetti':
                        spaghetti_index = i
                        break
                if spaghetti_index is None:
                    continue
                if abs(spaghetti_index - peter_index) != 1:
                    continue
                
                found = True
                solution = (n_perm, m_perm, l_perm)
                break
            if found:
                break
        if found:
            break
    
    if not found:
        print('{"solution": {}}')
        return
    
    rows = []
    for i in range(3):
        row = [str(i+1), solution[0][i], solution[1][i], solution[2][i]]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "name", "mothers' names", "lunch"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()