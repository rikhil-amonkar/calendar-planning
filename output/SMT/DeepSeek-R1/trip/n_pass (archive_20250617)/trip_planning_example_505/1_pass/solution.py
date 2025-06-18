from z3 import *

def main():
    n_days = 8
    city_names = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
    n_cities = len(city_names)
    
    flights_raw = [(1, 2), (0, 4), (3, 1), (3, 2), (2, 0), (3, 0)]
    connected = set()
    for (u, v) in flights_raw:
        connected.add((u, v))
        connected.add((v, u))
    
    Start = [Int('Start_%d' % (d+1)) for d in range(n_days)]
    End = [Int('End_%d' % (d+1)) for d in range(n_days)]
    Travel = [Bool('Travel_%d' % (d+1)) for d in range(n_days)]
    In = [[Bool('In_%s_%d' % (city_names[c], d+1)) for d in range(n_days)] for c in range(n_cities)]
    
    s = Solver()
    
    s.add(Start[0] >= 0, Start[0] < n_cities)
    
    for i in range(n_days):
        s.add(Start[i] >= 0, Start[i] < n_cities)
        s.add(End[i] >= 0, End[i] < n_cities)
        
        s.add(Or([And(Start[i] == c, In[c][i]) for c in range(n_cities)]))
        
        num_cities = Sum([If(In[c][i], 1, 0) for c in range(n_cities)])
        s.add(Travel[i] == (num_cities == 2))
        
        s.add(Implies(Not(Travel[i]), And(*[In[c][i] == (c == Start[i]) for c in range(n_cities)])))
        s.add(Implies(Not(Travel[i]), End[i] == Start[i]))
        
        s.add(Implies(Travel[i], In[End[i]][i]))
        s.add(Implies(Travel[i], End[i] != Start[i]))
        
        flight_cond = Or([And(Start[i] == c1, End[i] == c2) for (c1, c2) in connected])
        s.add(Implies(Travel[i], flight_cond))
    
    for i in range(n_days - 1):
        s.add(Start[i+1] == End[i])
    
    total_days = [Sum([If(In[c][d], 1, 0) for d in range(n_days)]) for c in range(n_cities)]
    s.add(total_days[0] == 4)
    s.add(total_days[1] == 2)
    s.add(total_days[2] == 2)
    s.add(total_days[3] == 2)
    s.add(total_days[4] == 2)
    
    s.add(In[1][1] == True)
    s.add(In[1][2] == True)
    s.add(In[2][2] == True)
    s.add(In[2][3] == True)
    
    if s.check() == sat:
        m = s.model()
        print("Found a valid schedule:")
        for d in range(n_days):
            cities_on_day = [city_names[c] for c in range(n_cities) if m.evaluate(In[c][d])]
            print(f"Day {d+1}: {', '.join(cities_on_day)}")
    else:
        print("No valid schedule found.")

if __name__ == "__main__":
    main()