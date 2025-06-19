from z3 import *

def main():
    cities = ['Warsaw', 'Venice', 'Vilnius', 'Salzburg', 'Amsterdam', 'Barcelona', 'Paris', 'Hamburg', 'Florence', 'Tallinn']
    
    flight_pairs = [
        ('Paris', 'Venice'),
        ('Barcelona', 'Amsterdam'),
        ('Amsterdam', 'Warsaw'),
        ('Amsterdam', 'Vilnius'),
        ('Barcelona', 'Warsaw'),
        ('Warsaw', 'Venice'),
        ('Amsterdam', 'Hamburg'),
        ('Barcelona', 'Hamburg'),
        ('Barcelona', 'Florence'),
        ('Barcelona', 'Venice'),
        ('Paris', 'Hamburg'),
        ('Paris', 'Vilnius'),
        ('Paris', 'Amsterdam'),
        ('Paris', 'Florence'),
        ('Florence', 'Amsterdam'),
        ('Vilnius', 'Warsaw'),
        ('Barcelona', 'Tallinn'),
        ('Paris', 'Warsaw'),
        ('Tallinn', 'Warsaw'),
        ('Tallinn', 'Vilnius'),
        ('Amsterdam', 'Tallinn'),
        ('Paris', 'Tallinn'),
        ('Paris', 'Barcelona'),
        ('Venice', 'Hamburg'),
        ('Warsaw', 'Hamburg'),
        ('Hamburg', 'Salzburg'),
        ('Amsterdam', 'Venice')
    ]
    
    flight_set = set()
    for (a, b) in flight_pairs:
        flight_set.add((min(a, b), max(a, b)))
        flight_set.add((max(a, b), min(a, b)))
    
    unconnected_pairs = []
    for i in range(len(cities)):
        for j in range(i + 1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            if (c1, c2) not in flight_set and (c2, c1) not in flight_set:
                unconnected_pairs.append((c1, c2))
    
    In = {}
    for c in cities:
        for d in range(1, 26):
            In[(c, d)] = Bool(f"In_{c}_{d}")
    
    s = Solver()
    
    for d in range(1, 26):
        if d == 1 or d == 25:
            s.add(Sum([If(In[(c, d)], 1, 0) for c in cities]) == 1)
        else:
            total = Sum([If(In[(c, d)], 1, 0) for c in cities])
            s.add(Or(total == 1, total == 2))
    
    for (c1, c2) in unconnected_pairs:
        for d in range(1, 26):
            s.add(Not(And(In[(c1, d)], In[(c2, d)])))
    
    for d in range(2, 25):
        total_d = Sum([If(In[(c, d)], 1, 0) for c in cities])
        for c in cities:
            s.add(Implies(And(In[(c, d)], total_d == 1), 
                          And(In[(c, d-1)], In[(c, d+1)])))
        
        inter_prev = Sum([If(And(In[(c, d)], In[(c, d-1)]), 1, 0) for c in cities])
        inter_next = Sum([If(And(In[(c, d)], In[(c, d+1)]), 1, 0) for c in cities])
        s.add(Implies(total_d == 2, And(inter_prev == 1, inter_next == 1)))
    
    # City duration constraints
    s.add(Sum([If(In[('Warsaw', d)], 1, 0) for d in range(1, 26)]) == 4)
    s.add(Sum([If(In[('Venice', d)], 1, 0) for d in range(1, 26)]) == 3)
    s.add(Sum([If(In[('Vilnius', d)], 1, 0) for d in range(1, 26)]) == 3)
    s.add(Sum([If(In[('Salzburg', d)], 1, 0) for d in range(1, 26)]) == 4)
    s.add(And(In[('Salzburg', 22)], In[('Salzburg', 23)], In[('Salzburg', 24)], In[('Salzburg', 25)]))
    s.add(Sum([If(In[('Amsterdam', d)], 1, 0) for d in range(1, 26)]) == 2)
    s.add(Sum([If(In[('Barcelona', d)], 1, 0) for d in range(1, 26)]) == 5)
    s.add(Or([In[('Barcelona', d)] for d in range(2, 7)]))
    s.add(Sum([If(In[('Paris', d)], 1, 0) for d in range(1, 26)]) == 2)
    s.add(And(In[('Paris', 1)], In[('Paris', 2)]))
    s.add(Sum([If(In[('Hamburg', d)], 1, 0) for d in range(1, 26)]) == 4)
    s.add(And(In[('Hamburg', 19)], In[('Hamburg', 20)], In[('Hamburg', 21)], In[('Hamburg', 22)]))
    s.add(Sum([If(In[('Florence', d)], 1, 0) for d in range(1, 26)]) == 5)
    s.add(Sum([If(In[('Tallinn', d)], 1, 0) for d in range(1, 26)]) == 2)
    s.add(If(In[('Tallinn', 11)], 1, 0) + If(In[('Tallinn', 12)], 1, 0) == 1)
    
    # Critical fixes: Ensure exclusive presence on last day of events
    s.add(Sum([If(In[(c, 2)], 1, 0) for c in cities]) == 1)  # Only in Paris on day 2
    s.add(Sum([If(In[(c, 22)], 1, 0) for c in cities]) == 1)  # Only in Hamburg on day 22
    
    if s.check() == sat:
        m = s.model()
        for d in range(1, 26):
            cities_on_day = []
            for c in cities:
                if m.evaluate(In[(c, d)]):
                    cities_on_day.append(c)
            print(f"Day {d}: {', '.join(cities_on_day)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()