from z3 import *

def main():
    total_days = 12
    max_stays = 5

    adjacencies = {
        "Brussels": ["Amsterdam", "Cologne", "Paris", "London"],
        "Amsterdam": ["Brussels", "Cologne"],
        "Cologne": ["Brussels", "Amsterdam", "Paris"],
        "Paris": ["Brussels", "Cologne", "Bordeaux", "Lyon"],
        "Bordeaux": ["Paris", "Lyon", "Toulouse", "Barcelona"],
        "Lyon": ["Paris", "Bordeaux", "Toulouse", "Marseille", "Geneva"],
        "Toulouse": ["Bordeaux", "Lyon", "Marseille", "Barcelona"],
        "Marseille": ["Lyon", "Toulouse", "Barcelona", "Geneva", "Milan"],
        "Barcelona": ["Bordeaux", "Toulouse", "Marseille", "Split"],
        "Geneva": ["Lyon", "Marseille", "Milan"],
        "Milan": ["Geneva", "Marseille", "Florence", "Venice"],
        "Florence": ["Milan", "Venice", "Rome"],
        "Venice": ["Milan", "Florence", "Rome"],
        "Rome": ["Florence", "Venice", "Naples"],
        "Naples": ["Rome"],
        "Split": ["Barcelona", "Budapest"],
        "Budapest": ["Split"]
    }
    
    cities = list(adjacencies.keys())
    adj_edges = []
    for city, neighbors in adjacencies.items():
        for n in neighbors:
            adj_edges.append((city, n))
    
    s = Solver()
    
    class Stay:
        def __init__(self, name):
            self.start = Int(f'{name}_start')
            self.end = Int(f'{name}_end')
            self.city = String(f'{name}_city')
    
    stays = [Stay(f'stay_{i}') for i in range(max_stays)]
    active = [Bool(f'active_{i}') for i in range(max_stays)]
    
    s.add(active[0] == True)
    
    for i in range(max_stays-1):
        s.add(Implies(Not(active[i]), Not(active[i+1])))
    
    for i in range(max_stays):
        s.add(Implies(Not(active[i]), stays[i].city == StringVal("None")))
        s.add(Implies(Not(active[i]), stays[i].start == 0))
        s.add(Implies(Not(active[i]), stays[i].end == 0))
        s.add(Implies(active[i], stays[i].start >= 1))
        s.add(Implies(active[i], stays[i].end <= total_days))
        s.add(Implies(active[i], stays[i].start <= stays[i].end))
        s.add(Implies(active[i], Or([stays[i].city == StringVal(c) for c in cities])))
    
    s.add(stays[0].start == 1)
    
    last_end = stays[0].end
    for i in range(1, max_stays):
        last_end = If(active[i], stays[i].end, last_end)
    s.add(last_end == total_days)
    
    for i in range(max_stays-1):
        s.add(Implies(And(active[i], active[i+1]), stays[i].end + 1 == stays[i+1].start))
    
    for i in range(max_stays-1):
        edge_constraints = []
        for (c1, c2) in adj_edges:
            edge_constraints.append(And(stays[i].city == StringVal(c1), stays[i+1].city == StringVal(c2)))
        s.add(Implies(And(active[i], active[i+1]), 
                    Or(stays[i].city == stays[i+1].city, 
                       Or(edge_constraints))))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(max_stays):
            if m.evaluate(active[i]):
                start = m.evaluate(stays[i].start)
                end = m.evaluate(stays[i].end)
                city = m.evaluate(stays[i].city)
                itinerary.append({
                    'day_range': f'Day {start}-{end}',
                    'place': city.as_string()
                })
        print(f'Plan found: {itinerary}')
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()