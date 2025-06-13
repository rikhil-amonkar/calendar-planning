from z3 import *

def main():
    cities = ['Lyon', 'Paris', 'Riga', 'Berlin', 'Stockholm', 'Zurich', 'Nice', 'Seville', 'Milan', 'Naples']
    req = [3, 5, 2, 2, 3, 5, 2, 3, 3, 4]
    
    flight_pairs = [
        ('Paris', 'Stockholm'),
        ('Seville', 'Paris'),
        ('Naples', 'Zurich'),
        ('Nice', 'Riga'),
        ('Berlin', 'Milan'),
        ('Paris', 'Zurich'),
        ('Paris', 'Nice'),
        ('Milan', 'Paris'),
        ('Milan', 'Riga'),
        ('Paris', 'Lyon'),
        ('Milan', 'Naples'),
        ('Paris', 'Riga'),
        ('Berlin', 'Stockholm'),
        ('Stockholm', 'Riga'),
        ('Nice', 'Zurich'),
        ('Milan', 'Zurich'),
        ('Lyon', 'Nice'),
        ('Zurich', 'Stockholm'),
        ('Zurich', 'Riga'),
        ('Berlin', 'Naples'),
        ('Milan', 'Stockholm'),
        ('Berlin', 'Zurich'),
        ('Milan', 'Seville'),
        ('Paris', 'Naples'),
        ('Berlin', 'Riga'),
        ('Nice', 'Stockholm'),
        ('Berlin', 'Paris'),
        ('Nice', 'Naples'),
        ('Berlin', 'Nice')
    ]
    
    flight_set = set()
    for (c1, c2) in flight_pairs:
        key = (min(c1, c2), max(c1, c2))
        flight_set.add(key)
    
    num_days = 23
    num_cities = len(cities)
    
    In = [[Bool(f'In_{d}_{c}') for c in range(num_cities)] for d in range(num_days)]
    
    s = Solver()
    
    for d in range(num_days):
        num_in_day = Sum([If(In[d][c], 1, 0) for c in range(num_cities)])
        s.add(Or(num_in_day == 1, num_in_day == 2))
    
    for c_index in range(num_cities):
        total_days = Sum([If(In[d][c_index], 1, 0) for d in range(num_days)])
        s.add(total_days == req[c_index])
    
    berlin_index = cities.index('Berlin')
    s.add(In[0][berlin_index])
    s.add(In[1][berlin_index])
    # Ensure only Berlin on days 1 and 2
    for d in [0, 1]:
        for c_index in range(num_cities):
            if c_index != berlin_index:
                s.add(Not(In[d][c_index]))
    
    stockholm_index = cities.index('Stockholm')
    s.add(In[19][stockholm_index])
    s.add(In[20][stockholm_index])
    s.add(In[21][stockholm_index])
    # Ensure only Stockholm on days 20-22
    for d in [19, 20, 21]:
        for c_index in range(num_cities):
            if c_index != stockholm_index:
                s.add(Not(In[d][c_index]))
    
    nice_index = cities.index('Nice')
    s.add(In[11][nice_index])
    s.add(In[12][nice_index])
    # Ensure only Nice on days 12-13
    for d in [11, 12]:
        for c_index in range(num_cities):
            if c_index != nice_index:
                s.add(Not(In[d][c_index]))
    
    for d in range(num_days):
        for i in range(num_cities):
            for j in range(i + 1, num_cities):
                city_i = cities[i]
                city_j = cities[j]
                key = (min(city_i, city_j), max(city_i, city_j))
                if key not in flight_set:
                    s.add(Not(And(In[d][i], In[d][j])))
    
    for c_index in range(num_cities):
        for d in range(num_days - 1):
            leave_condition = And(In[d][c_index], Not(In[d+1][c_index]))
            other_cities_leave = [In[d][j] for j in range(num_cities) if j != c_index]
            if other_cities_leave:
                s.add(Implies(leave_condition, Or(other_cities_leave)))
            
            arrive_condition = And(Not(In[d][c_index]), In[d+1][c_index])
            other_cities_arrive = [In[d+1][j] for j in range(num_cities) if j != c_index]
            if other_cities_arrive:
                s.add(Implies(arrive_condition, Or(other_cities_arrive)))
    
    if s.check() == sat:
        m = s.model()
        for d in range(num_days):
            cities_today = []
            for c_index in range(num_cities):
                if is_true(m.evaluate(In[d][c_index])):
                    cities_today.append(cities[c_index])
            print(f"Day {d + 1}: {', '.join(cities_today)}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()