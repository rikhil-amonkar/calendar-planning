from z3 import *
import json

def main():
    cities = ['Dublin', 'Helsinki', 'Hamburg', 'London', 'Mykonos', 'Reykjavik']
    
    edges = [
        ('Dublin', 'London'),
        ('Hamburg', 'Dublin'),
        ('Helsinki', 'Reykjavik'),
        ('Hamburg', 'London'),
        ('Dublin', 'Helsinki'),
        ('Reykjavik', 'London'),
        ('London', 'Mykonos'),
        ('Dublin', 'Reykjavik'),
        ('Hamburg', 'Helsinki'),
        ('Helsinki', 'London')
    ]
    
    graph = {c: set() for c in cities}
    for (u, v) in edges:
        graph[u].add(v)
        graph[v].add(u)
    
    non_edges = []
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            if c2 not in graph[c1]:
                non_edges.append((c1, c2))
    
    s = Solver()
    
    In = {}
    for c in cities:
        for d in range(1, 17):
            In[(c, d)] = Bool(f'In_{c}_{d}')
    
    for d in range(1, 17):
        total = Sum([If(In[(c, d)], 1, 0) for c in cities])
        s.add(Or(total == 1, total == 2))
        
        for (c1, c2) in non_edges:
            s.add(Not(And(In[(c1, d)], In[(c2, d)])))
    
    flight_day_indicators = []
    for d in range(1, 17):
        flight_day_indicators.append(If(Sum([If(In[(c, d)], 1, 0) for c in cities]) == 2, 1, 0))
    s.add(Sum(flight_day_indicators) == 5)
    
    for d in range(1, 17):
        if 2 <= d <= 6:
            s.add(In[('Dublin', d)] == True)
        else:
            s.add(In[('Dublin', d)] == False)
    
    for d in range(1, 17):
        if d in [9, 10]:
            s.add(In[('Reykjavik', d)] == True)
        else:
            s.add(In[('Reykjavik', d)] == False)
    
    s.add(Sum([If(In[('Hamburg', d)], 1, 0) for d in range(1,17)]) == 2)
    s.add(Or(In[('Hamburg', 1)], In[('Hamburg', 2)]))
    
    s.add(Sum([If(In[('Mykonos', d)], 1, 0) for d in range(1,17)]) == 3)
    s.add(Sum([If(In[('London', d)], 1, 0) for d in range(1,17)]) == 5)
    s.add(Sum([If(In[('Helsinki', d)], 1, 0) for d in range(1,17)]) == 4)
    
    if s.check() == sat:
        m = s.model()
        flight_days = []
        for d in range(1, 17):
            count = 0
            for c in cities:
                if m.evaluate(In[(c, d)]):
                    count += 1
            if count == 2:
                flight_days.append(d)
                
        records = []
        for c in cities:
            days_present = []
            for d in range(1, 17):
                if m.evaluate(In[(c, d)], model_completion=True):
                    days_present.append(d)
            if not days_present:
                continue
            days_present.sort()
            blocks = []
            start = days_present[0]
            end = start
            for i in range(1, len(days_present)):
                if days_present[i] == end + 1:
                    end = days_present[i]
                else:
                    blocks.append((start, end))
                    start = days_present[i]
                    end = days_present[i]
            blocks.append((start, end))
            
            for (s_block, e_block) in blocks:
                if s_block == e_block:
                    day_str = f"Day {s_block}"
                else:
                    day_str = f"Day {s_block}-{e_block}"
                records.append((s_block, e_block, day_str, c))
        
        for d in flight_days:
            for c in cities:
                if m.evaluate(In[(c, d)], model_completion=True):
                    records.append((d, d, f"Day {d}", c))
        
        records.sort(key=lambda x: (x[0], x[1]))
        itinerary_list = [{"day_range": day_str, "place": c} for s_val, e_val, day_str, c in records]
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()