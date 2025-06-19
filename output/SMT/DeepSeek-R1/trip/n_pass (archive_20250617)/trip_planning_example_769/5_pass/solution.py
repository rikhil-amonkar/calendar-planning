from z3 import *

def main():
    City = Datatype('City')
    City.declare('Porto')
    City.declare('Prague')
    City.declare('Reykjavik')
    City.declare('Santorini')
    City.declare('Amsterdam')
    City.declare('Munich')
    City = City.create()
    
    city_names = {
        City.Porto: "Porto",
        City.Prague: "Prague",
        City.Reykjavik: "Reykjavik",
        City.Santorini: "Santorini",
        City.Amsterdam: "Amsterdam",
        City.Munich: "Munich"
    }
    
    req_days = {
        City.Porto: 5,
        City.Prague: 4,
        City.Reykjavik: 4,
        City.Santorini: 2,
        City.Amsterdam: 2,
        City.Munich: 4
    }
    
    connections_str = [
        ('Porto', 'Amsterdam'),
        ('Munich', 'Amsterdam'),
        ('Reykjavik', 'Amsterdam'),
        ('Munich', 'Porto'),
        ('Prague', 'Reykjavik'),
        ('Reykjavik', 'Munich'),
        ('Amsterdam', 'Santorini'),
        ('Prague', 'Amsterdam'),
        ('Prague', 'Munich')
    ]
    
    allowed_pairs = []
    for a_str, b_str in connections_str:
        a_const = getattr(City, a_str)
        b_const = getattr(City, b_str)
        allowed_pairs.append((a_const, b_const))
        allowed_pairs.append((b_const, a_const))
    
    num_days = 16
    days = list(range(num_days))
    
    start = [Const(f'start_{i}', City) for i in days]
    end = [Const(f'end_{i}', City) for i in days]
    
    s = Solver()
    
    for i in days:
        no_flight = (start[i] == end[i])
        flight_options = []
        for (a, b) in allowed_pairs:
            flight_options.append(And(start[i] == a, end[i] == b))
        flight = Or(flight_options)
        s.add(Or(no_flight, flight))
    
    for i in range(1, num_days):
        s.add(start[i] == end[i-1])
    
    for city, total_req in req_days.items():
        total_days = 0
        for i in days:
            total_days += If(Or(start[i] == city, end[i] == city), 1, 0)
        s.add(total_days == total_req)
    
    wedding_days = [3, 4, 5, 6]
    wedding_constraint = Or([And(start[i] == City.Reykjavik, end[i] == City.Reykjavik) for i in wedding_days])
    s.add(wedding_constraint)
    
    s.add(And(start[13] == City.Amsterdam, end[13] == City.Amsterdam))
    s.add(And(start[14] == City.Amsterdam, end[14] == City.Amsterdam))
    
    meeting_days = [6, 7, 8, 9]
    meeting_constraint = Or([And(start[i] == City.Munich, end[i] == City.Munich) for i in meeting_days])
    s.add(meeting_constraint)
    
    if s.check() == sat:
        model = s.model()
        for i in days:
            start_val = model.eval(start[i])
            end_val = model.eval(end[i])
            start_name = city_names[start_val]
            end_name = city_names[end_val]
            if start_val == end_val:
                print(f"Day {i+1}: Stay in {start_name}")
            else:
                print(f"Day {i+1}: Fly from {start_name} to {end_name}")
        
        print("\nTotal days per city:")
        for city in req_days:
            count = 0
            for i in days:
                if model.eval(Or(start[i] == city, end[i] == city)):
                    count += 1
            print(f"{city_names[city]}: {count} days")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()