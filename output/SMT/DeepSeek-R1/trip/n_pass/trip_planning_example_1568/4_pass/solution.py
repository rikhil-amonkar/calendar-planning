from z3 import *

def main():
    n_days = 20
    cities = ["Prague", "Brussels", "Riga", "Munich", "Seville", "Stockholm", "Istanbul", "Amsterdam", "Vienna", "Split"]
    
    days_required = {
        "Prague": 5,
        "Brussels": 2,
        "Riga": 2,
        "Munich": 2,
        "Seville": 3,
        "Stockholm": 2,
        "Istanbul": 2,
        "Amsterdam": 3,
        "Vienna": 5,
        "Split": 3
    }
    
    flights = [
        ("Riga", "Stockholm"),
        ("Stockholm", "Brussels"),
        ("Istanbul", "Munich"),
        ("Istanbul", "Riga"),
        ("Prague", "Split"),
        ("Vienna", "Brussels"),
        ("Vienna", "Riga"),
        ("Split", "Stockholm"),
        ("Munich", "Amsterdam"),
        ("Split", "Amsterdam"),
        ("Amsterdam", "Stockholm"),
        ("Amsterdam", "Riga"),
        ("Vienna", "Stockholm"),
        ("Vienna", "Istanbul"),
        ("Vienna", "Seville"),
        ("Istanbul", "Amsterdam"),
        ("Munich", "Brussels"),
        ("Prague", "Munich"),
        ("Riga", "Munich"),
        ("Prague", "Amsterdam"),
        ("Prague", "Brussels"),
        ("Prague", "Istanbul"),
        ("Istanbul", "Stockholm"),
        ("Vienna", "Prague"),
        ("Munich", "Split"),
        ("Vienna", "Amsterdam"),
        ("Prague", "Stockholm"),
        ("Brussels", "Seville"),
        ("Munich", "Stockholm"),
        ("Istanbul", "Brussels"),
        ("Amsterdam", "Seville"),
        ("Vienna", "Split"),
        ("Munich", "Seville"),
        ("Riga", "Brussels"),
        ("Prague", "Riga"),
        ("Vienna", "Munich")
    ]
    
    flight_set = set()
    for u, v in flights:
        flight_set.add(frozenset({u, v}))
    
    In = {c: [Bool(f"In_{c}_{d}") for d in range(1, n_days+1)] for c in cities}
    
    s = Solver()
    
    # Fixed constraints for Prague: days 5-9
    for t in [5, 6, 7, 8, 9]:
        s.add(In["Prague"][t-1])
    
    # Fixed constraints for Stockholm: days 16-17
    for t in [16, 17]:
        s.add(In["Stockholm"][t-1])
    
    # At least one of day 15 or 16 in Riga
    s.add(Or(In["Riga"][14], In["Riga"][15]))
    
    # At least one of days 1-5 in Vienna
    s.add(Or([In["Vienna"][t] for t in range(0, 5)]))
    
    # At least one of days 11-13 in Split
    s.add(Or([In["Split"][t] for t in range(10, 13)]))
    
    # Total days per city
    for c in cities:
        total_days = days_required[c]
        s.add(Sum([If(In[c][t], 1, 0) for t in range(n_days)]) == total_days)
    
    # Each day: at least one city, at most two cities, and if two cities, they must be connected by a direct flight
    for t in range(n_days):
        in_cities = [In[c][t] for c in cities]
        s.add(Sum([If(v, 1, 0) for v in in_cities]) >= 1)
        s.add(Sum([If(v, 1, 0) for v in in_cities]) <= 2)
        
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if frozenset({c1, c2}) not in flight_set:
                    s.add(Not(And(In[c1][t], In[c2][t])))
    
    # Continuity constraints for days 1 to 18 (0-indexed: indices 1 to 18)
    for c in cities:
        for t in range(1, n_days-1):
            s.add(Implies(And(In[c][t], Not(In[c][t-1])), In[c][t+1]))
            s.add(Implies(And(In[c][t], Not(In[c][t+1])), In[c][t-1]))
    
    # Departure constraint: if in a city on day t and not on day t+1, then must be another city on day t connected by flight
    for c in cities:
        for t in range(n_days-1):
            other_city_exists = Or([And(In[d][t], d != c) for d in cities])
            s.add(Implies(And(In[c][t], Not(In[c][t+1])), other_city_exists))
    
    # Ensure that if leaving a city, the next day must have exactly two cities including the departure city
    for c in cities:
        for t in range(n_days-1):
            if t < n_days-1:
                leave_condition = And(In[c][t], Not(In[c][t+1]))
                exactly_two_next_day = And(
                    Sum([If(In[d][t+1], 1, 0) for d in cities]) == 2,
                    In[c][t+1]
                )
                s.add(Implies(leave_condition, exactly_two_next_day))
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        schedule = []
        for day in range(1, n_days+1):
            current_cities = []
            for c in cities:
                if model.evaluate(In[c][day-1]):
                    current_cities.append(c)
            schedule.append((day, current_cities))
        
        # Print the schedule
        for day, cities_list in schedule:
            print(f"Day {day}: {', '.join(cities_list)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()