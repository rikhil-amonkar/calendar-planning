from z3 import *

def main():
    s = Solver()
    cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
    
    in_city = {}
    for city in cities:
        in_city[city] = [ Bool(f"in_{city}_{i+1}") for i in range(15) ]
    
    # Constraint: Each day, at least one city is visited
    for i in range(15):
        s.add(Or([in_city[city][i] for city in cities]))
    
    # Constraint: At most two cities per day
    for i in range(15):
        for c1 in range(len(cities)):
            for c2 in range(c1+1, len(cities)):
                for c3 in range(c2+1, len(cities)):
                    s.add(Not(And(in_city[cities[c1]][i], in_city[cities[c2]][i], in_city[cities[c3]][i])))
    
    # Constraint: Consecutive days must share at least one city
    for i in range(14):
        s.add(Or([And(in_city[city][i], in_city[city][i+1]) for city in cities]))
    
    # Constraint: Bucharest and Seville cannot be together on the same day
    for i in range(15):
        s.add(Not(And(in_city['Bucharest'][i], in_city['Seville'][i])))
    
    # Constraint: Madrid on days 1-7 and not on days 8-15
    for i in range(7):
        s.add(in_city['Madrid'][i] == True)
    for i in range(7, 15):
        s.add(in_city['Madrid'][i] == False)
    
    # Constraint: Bucharest on days 14-15 and not on days 1-13
    for i in range(13):
        s.add(in_city['Bucharest'][i] == False)
    for i in range(13, 15):
        s.add(in_city['Bucharest'][i] == True)
    
    # Constraint: Total days in Paris = 6 and Seville = 3
    total_paris = Sum([If(in_city['Paris'][i], 1, 0) for i in range(15)])
    s.add(total_paris == 6)
    
    total_seville = Sum([If(in_city['Seville'][i], 1, 0) for i in range(15)])
    s.add(total_seville == 3)
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i in range(15):
            day = i + 1
            cities_today = []
            for city in cities:
                if m.evaluate(in_city[city][i]):
                    cities_today.append(city)
            schedule.append((day, cities_today))
        
        for day, cities_list in schedule:
            print(f"Day {day}: {', '.join(cities_list)}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()