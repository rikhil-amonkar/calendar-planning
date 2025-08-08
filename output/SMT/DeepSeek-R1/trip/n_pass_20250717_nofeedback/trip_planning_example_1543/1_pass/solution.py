from z3 import *

def main():
    city_names = ['Prague', 'Warsaw', 'Dublin', 'Athens', 'Vilnius', 'Porto', 'London', 'Seville', 'Lisbon', 'Dubrovnik']
    City = Datatype('City')
    for name in city_names:
        City.declare(name)
    City = City.create()
    city_consts = [getattr(City, name) for name in city_names]
    city_map = {const: name for const, name in zip(city_consts, city_names)}
    
    flight_pairs = [
        ('Warsaw', 'Vilnius'),
        ('Prague', 'Athens'),
        ('London', 'Lisbon'),
        ('Lisbon', 'Porto'),
        ('Prague', 'Lisbon'),
        ('London', 'Dublin'),
        ('Athens', 'Vilnius'),
        ('Athens', 'Dublin'),
        ('Prague', 'London'),
        ('London', 'Warsaw'),
        ('Dublin', 'Seville'),
        ('Seville', 'Porto'),
        ('Lisbon', 'Athens'),
        ('Dublin', 'Porto'),
        ('Athens', 'Warsaw'),
        ('Lisbon', 'Warsaw'),
        ('Porto', 'Warsaw'),
        ('Prague', 'Warsaw'),
        ('Prague', 'Dublin'),
        ('Athens', 'Dubrovnik'),
        ('Lisbon', 'Dublin'),
        ('Dubrovnik', 'Dublin'),
        ('Lisbon', 'Seville'),
        ('London', 'Athens')
    ]
    flight_set = set()
    for (a, b) in flight_pairs:
        a_const = getattr(City, a)
        b_const = getattr(City, b)
        flight_set.add((a_const, b_const))
        flight_set.add((b_const, a_const))
    
    start_city = [Const(f'start_city_{i}', City) for i in range(26)]
    end_city = [Const(f'end_city_{i}', City) for i in range(26)]
    
    s = Solver()
    
    # Fixed constraints
    s.add(start_city[0] == City.Prague)
    s.add(end_city[0] == City.Prague)
    s.add(start_city[1] == City.Prague)
    s.add(end_city[1] == City.Prague)
    s.add(start_city[2] == City.Prague)
    s.add(end_city[2] == City.London)
    s.add(start_city[3] == City.London)
    s.add(end_city[3] == City.London)
    s.add(start_city[4] == City.London)
    s.add(end_city[4] == City.Lisbon)
    s.add(start_city[5] == City.Lisbon)
    s.add(end_city[5] == City.Lisbon)
    s.add(start_city[6] == City.Lisbon)
    s.add(end_city[6] == City.Lisbon)
    s.add(start_city[7] == City.Lisbon)
    s.add(end_city[7] == City.Lisbon)
    s.add(start_city[8] == City.Lisbon)
    s.add(end_city[15] == City.Porto)
    s.add(start_city[16] == City.Porto)
    s.add(end_city[16] == City.Porto)
    s.add(start_city[17] == City.Porto)
    s.add(end_city[17] == City.Porto)
    s.add(start_city[18] == City.Porto)
    s.add(end_city[18] == City.Porto)
    s.add(start_city[19] == City.Porto)
    s.add(end_city[19] == City.Warsaw)
    s.add(start_city[20] == City.Warsaw)
    s.add(end_city[20] == City.Warsaw)
    s.add(start_city[21] == City.Warsaw)
    s.add(end_city[21] == City.Warsaw)
    s.add(start_city[22] == City.Warsaw)
    s.add(end_city[22] == City.Warsaw)
    
    # Continuity constraints
    for i in range(25):
        s.add(end_city[i] == start_city[i+1])
    
    # Flight constraints
    for i in range(26):
        flight_taken = (start_city[i] != end_city[i])
        allowed_flight = Or([And(start_city[i] == a, end_city[i] == b) for (a, b) in flight_set])
        s.add(Implies(flight_taken, allowed_flight))
    
    # Total days per city
    total_days = {city: 0 for city in city_consts}
    for city in city_consts:
        total_days[city] = sum([If(Or(start_city[i] == city, end_city[i] == city), 1, 0) for i in range(26)])
    s.add(total_days[City.Prague] == 3)
    s.add(total_days[City.Warsaw] == 4)
    s.add(total_days[City.Dublin] == 3)
    s.add(total_days[City.Athens] == 3)
    s.add(total_days[City.Vilnius] == 4)
    s.add(total_days[City.Porto] == 5)
    s.add(total_days[City.London] == 3)
    s.add(total_days[City.Seville] == 2)
    s.add(total_days[City.Lisbon] == 5)
    s.add(total_days[City.Dubrovnik] == 3)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for day in range(1, 27):
            i = day - 1
            start_val = model.eval(start_city[i])
            end_val = model.eval(end_city[i])
            start_name = city_map.get(start_val, "Unknown")
            end_name = city_map.get(end_val, "Unknown")
            itinerary_list.append({"day": day, "place": start_name})
            if start_val != end_val:
                itinerary_list.append({"day": day, "place": end_name})
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()