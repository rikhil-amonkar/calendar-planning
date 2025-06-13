from z3 import *

def main():
    cities = ['Tallinn', 'Bucharest', 'Seville', 'Stockholm', 'Munich', 'Milan']
    edges_list = [
        ('Milan', 'Stockholm'),
        ('Munich', 'Stockholm'),
        ('Bucharest', 'Munich'),
        ('Munich', 'Seville'),
        ('Stockholm', 'Tallinn'),
        ('Munich', 'Milan'),
        ('Munich', 'Tallinn'),
        ('Seville', 'Milan')
    ]
    normalized_edges = set(tuple(sorted(edge)) for edge in edges_list)
    
    non_edges = []
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            pair = tuple(sorted([c1, c2]))
            if pair not in normalized_edges:
                non_edges.append((c1, c2))
    
    s = Solver()
    present = {}
    for c in cities:
        present[c] = {}
        for d in range(1, 19):
            present[c][d] = Bool(f"{c}_{d}")
    
    for d in range(1, 5):
        s.add(present['Bucharest'][d] == True)
    for d in range(5, 19):
        s.add(present['Bucharest'][d] == False)
    
    for d in range(1, 4):
        s.add(present['Munich'][d] == False)
    for d in range(4, 9):
        s.add(present['Munich'][d] == True)
    for d in range(9, 19):
        s.add(present['Munich'][d] == False)
    
    for d in range(1, 8):
        s.add(present['Seville'][d] == False)
    for d in range(8, 13):
        s.add(present['Seville'][d] == True)
    for d in range(13, 19):
        s.add(present['Seville'][d] == False)
    
    for d in [1, 2, 3]:
        for c in cities:
            if c != 'Bucharest':
                s.add(present[c][d] == False)
    
    d4_exclude = ['Tallinn', 'Seville', 'Stockholm', 'Milan']
    for c in d4_exclude:
        s.add(present[c][4] == False)
    
    d8_exclude = ['Tallinn', 'Bucharest', 'Stockholm', 'Milan']
    for c in d8_exclude:
        s.add(present[c][8] == False)
    
    total_days = {}
    for c in cities:
        total_days[c] = 0
        for d in range(1, 19):
            total_days[c] += If(present[c][d], 1, 0)
    s.add(total_days['Tallinn'] == 2)
    s.add(total_days['Bucharest'] == 4)
    s.add(total_days['Seville'] == 5)
    s.add(total_days['Stockholm'] == 5)
    s.add(total_days['Munich'] == 5)
    s.add(total_days['Milan'] == 2)
    
    for d in range(1, 19):
        s.add(Or([present[c][d] for c in cities]))
    
    for d in range(1, 19):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    c1, c2, c3 = cities[i], cities[j], cities[k]
                    s.add(Not(And(present[c1][d], present[c2][d], present[c3][d])))
        for (c1, c2) in non_edges:
            s.add(Not(And(present[c1][d], present[c2][d])))
    
    for d in range(1, 18):
        s.add(Or([And(present[c][d], present[c][d+1]) for c in cities]))
    
    if s.check() == sat:
        m = s.model()
        for d in range(1, 19):
            cities_today = []
            for c in cities:
                if m.evaluate(present[c][d]):
                    cities_today.append(c)
            print(f"Day {d}: {', '.join(cities_today)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()