import itertools
import json

def main():
    names = ['Arnold', 'Eric', 'Peter']
    musics = ['pop', 'rock', 'classical']
    children = ['Fred', 'Meredith', 'Bella']
    books = ['mystery', 'romance', 'science fiction']
    
    def solve():
        for n_perm in itertools.permutations(names):
            if n_perm[0] != 'Peter':
                continue
            eric_index = n_perm.index('Eric')
            
            for m_perm in itertools.permutations(musics):
                if m_perm[eric_index] != 'classical':
                    continue
                    
                for c_perm in itertools.permutations(children):
                    if eric_index == 0 or c_perm[eric_index-1] != 'Fred':
                        continue
                        
                    for b_perm in itertools.permutations(books):
                        if b_perm[eric_index] != 'mystery':
                            continue
                            
                        sci_fi_index = b_perm.index('science fiction')
                        if c_perm[sci_fi_index] != 'Meredith':
                            continue
                            
                        romance_index = b_perm.index('romance')
                        rock_index = m_perm.index('rock')
                        if rock_index <= romance_index:
                            continue
                            
                        return (n_perm, m_perm, c_perm, b_perm)
        return None

    solution = solve()
    if solution is None:
        print(json.dumps({"error": "No solution found"}))
        return

    n_perm, m_perm, c_perm, b_perm = solution
    
    header = ["House", "Name", "Music", "Child", "Book"]
    rows = []
    for i in range(3):
        row = [str(i+1), n_perm[i], m_perm[i], c_perm[i], b_perm[i]]
        rows.append(row)
    
    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()