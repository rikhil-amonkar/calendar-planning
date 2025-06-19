from z3 import *

def main():
    s = Solver()
    cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
    
    in_city = {}
    for city in cities:
        in_city[city] = [ Bool(f"in_{city}_{i}") for i in range(15) ]
    
    # Constraint: Each day, at least one city is visited
    for i in range(15):
        s.add(Or(in_city['Paris'][i], in_city['Madrid'][i], in_city['Bucharest'][i], in_city['Seville'][i]))
    
    # Constraint: At most two cities per day
    for i in range(15):
        s.add(Not(And(in_city['Paris'][i], in_city['Madrid'][i], in_city['Bucharest'][i])))
        s.add(Not(And(in_city['Paris'][i], in_city['Madrid'][i], in_city['Seville'][i])))
        s.add(Not(And(in_city['Paris'][i], in_city['Bucharest'][i], in_city['Seville'][i])))
        s.add(Not(And(in_city['Madrid'][i], in_city['Bucharest'][i], in_city['Seville'][i])))
    
    # Constraint: Bucharest and Seville cannot be together on any day
    for i in range(15):
        s.add(Not(And(in_city['Bucharest'][i], in_city['Seville'][i])))
    
    # Constraint: Consecutive days must share at least one common city
    for i in range(14):
        s.add(Or(
            And(in_city['Paris'][i], in_city['Paris'][i+1]),
            And(in_city['Madrid'][i], in_city['Madrid'][i+1]),
            And(in_city['Bucharest'][i], in_city['Bucharest'][i+1]),
            And(in_city['Seville'][i], in_city['Seville'][i+1])
        ))
    
    # Constraint: Madrid must be visited on days 1-7 (indices 0-6) and not on days 8-15 (indices 7-14)
    for i in range(7):
        s.add(in_city['Madrid'][i] == True)
    for i in range(7, 15):
        s.add(in_city['Madrid'][i] == False)
    
    # Constraint: Bucharest must be visited on days 14-15 (indices 13-14) and not on days 1-13 (indices 0-12)
    for i in range(13):
        s.add(in_city['Bucharest'][i] == False)
    s.add(in_city['Bucharest'][13] == True)
    s.add(in_city['Bucharest'][14] == True)
    
    # Constraint: Total days in Paris = 6
    total_paris = Sum([If(in_city['Paris'][i], 1, 0) for i in range(15)])
    s.add(total_paris == 6)
    
    # Constraint: Total days in Seville = 3
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