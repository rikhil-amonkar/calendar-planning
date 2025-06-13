from z3 import *

def main():
    # Define the City enum
    City = Datatype('City')
    City.declare('Porto')
    City.declare('Stuttgart')
    City.declare('Seville')
    City.declare('Madrid')
    City = City.create()
    
    Porto = City.Porto
    Stuttgart = City.Stuttgart
    Seville = City.Seville
    Madrid = City.Madrid
    
    n_days = 13
    n_cities = 14  # c0 to c13 (14 points: start day1 to end day13)
    
    # City variables: c0, c1, ... c13
    c = [Const('c_%d' % i, City) for i in range(n_cities)]
    # Flight variables: flight0 to flight12 (for day1 to day13)
    flight = [Bool('flight_%d' % i) for i in range(n_days)]
    
    # Define direct flights (both directions)
    direct_flights = [(Porto, Stuttgart), (Seville, Porto), (Madrid, Porto), (Madrid, Seville)]
    allowed_edges = set()
    for u, v in direct_flights:
        allowed_edges.add((u, v))
        allowed_edges.add((v, u))
    
    s = Solver()
    
    # Flight constraints for each day
    for i in range(n_days):
        edge_constraints = []
        for u, v in allowed_edges:
            edge_constraints.append(And(c[i] == u, c[i+1] == v))
        s.add(If(flight[i],
                 And(c[i] != c[i+1], Or(edge_constraints)),
                 c[i] == c[i+1]))
    
    # Count days per city
    def count_city(city):
        total = 0
        for i in range(n_days):
            term1 = If(c[i] == city, 1, 0)
            term2 = If(And(flight[i], c[i+1] == city), 1, 0)
            total = total + term1 + term2
        return total
    
    s.add(count_city(Stuttgart) == 7)
    s.add(count_city(Seville) == 2)
    s.add(count_city(Porto) == 3)
    s.add(count_city(Madrid) == 4)
    
    # Conference in Stuttgart on day7 (i=6) and day13 (i=12)
    s.add(Or(c[6] == Stuttgart, c[7] == Stuttgart))  # day7: start c6, end c7
    s.add(Or(c[12] == Stuttgart, c[13] == Stuttgart)) # day13: start c12, end c13
    
    # Visit relatives in Madrid between day1 and day4 (c0 to c4)
    s.add(Or([c[i] == Madrid for i in range(5)]))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        city_names = {Porto: 'Porto', Stuttgart: 'Stuttgart', Seville: 'Seville', Madrid: 'Madrid'}
        
        # Print the plan
        for i in range(n_days):
            start_city = m.eval(c[i])
            end_city = m.eval(c[i+1])
            flight_taken = m.eval(flight[i])
            day = i + 1
            if flight_taken:
                print(f"Day {day}: Fly from {city_names[start_city]} to {city_names[end_city]}")
            else:
                print(f"Day {day}: Stay in {city_names[start_city]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()