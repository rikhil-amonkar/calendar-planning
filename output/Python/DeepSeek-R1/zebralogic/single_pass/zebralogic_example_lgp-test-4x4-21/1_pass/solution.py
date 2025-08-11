import itertools
import json

def main():
    names = ['Eric', 'Peter', 'Alice', 'Arnold']
    cars = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
    months = ['jan', 'april', 'sept', 'feb']
    hobbies = ['painting', 'cooking', 'gardening', 'photography']
    
    def constraint1(m):
        return m[1] != 'jan'
    
    def constraint2(n, h):
        idx_photo = h.index('photography')
        idx_eric = n.index('Eric')
        return idx_photo < idx_eric
    
    def constraint3(n, h):
        idx_photo = h.index('photography')
        idx_peter = n.index('Peter')
        return idx_photo < idx_peter
    
    def constraint4(c):
        idx_honda = c.index('honda civic')
        idx_tesla = c.index('tesla model 3')
        return idx_tesla == idx_honda + 1
    
    def constraint5(c, h):
        idx_tesla = c.index('tesla model 3')
        idx_garden = h.index('gardening')
        return abs(idx_tesla - idx_garden) == 2
    
    def constraint6(n, c):
        idx_tesla = c.index('tesla model 3')
        return n[idx_tesla] == 'Arnold'
    
    def constraint7(m, h):
        idx_feb = m.index('feb')
        return h[idx_feb] == 'cooking'
    
    def constraint8(n, c):
        idx_toyota = c.index('toyota camry')
        return n[idx_toyota] == 'Peter'
    
    def constraint9(n, m):
        idx_april = m.index('april')
        return n[idx_april] == 'Arnold'
    
    def constraint10(n, h):
        idx_alice = n.index('Alice')
        return h[idx_alice] == 'photography'
    
    def constraint11(n, m):
        idx_peter = n.index('Peter')
        return m[idx_peter] == 'jan'
    
    for n_perm in itertools.permutations(names):
        for c_perm in itertools.permutations(cars):
            if not constraint4(c_perm):
                continue
            if not constraint6(n_perm, c_perm):
                continue
            if not constraint8(n_perm, c_perm):
                continue
            for m_perm in itertools.permutations(months):
                if not constraint1(m_perm):
                    continue
                if not constraint9(n_perm, m_perm):
                    continue
                if not constraint11(n_perm, m_perm):
                    continue
                for h_perm in itertools.permutations(hobbies):
                    if not constraint2(n_perm, h_perm):
                        continue
                    if not constraint3(n_perm, h_perm):
                        continue
                    if not constraint5(c_perm, h_perm):
                        continue
                    if not constraint7(m_perm, h_perm):
                        continue
                    if not constraint10(n_perm, h_perm):
                        continue
                    
                    header = ["House", "Name", "Car", "Month", "Hobby"]
                    rows = []
                    for i in range(4):
                        row = [str(i+1), n_perm[i], c_perm[i], m_perm[i], h_perm[i]]
                        rows.append(row)
                    solution = {
                        "solution": {
                            "header": header,
                            "rows": rows
                        }
                    }
                    print(json.dumps(solution))
                    return
    print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()