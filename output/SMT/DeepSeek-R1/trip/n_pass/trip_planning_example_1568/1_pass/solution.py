from z3 import *
import json

def main():
    Cities = ['Vienna', 'Prague', 'Split', 'Riga', 'Stockholm', 'Brussels', 'Munich', 'Seville', 'Istanbul', 'Amsterdam']
    
    connections = [
        ('Riga','Stockholm'), ('Stockholm','Brussels'), ('Istanbul','Munich'), ('Istanbul','Riga'),
        ('Prague','Split'), ('Vienna','Brussels'), ('Vienna','Riga'), ('Split','Stockholm'),
        ('Munich','Amsterdam'), ('Split','Amsterdam'), ('Amsterdam','Stockholm'), ('Amsterdam','Riga'),
        ('Vienna','Stockholm'), ('Vienna','Istanbul'), ('Vienna','Seville'), ('Istanbul','Amsterdam'),
        ('Munich','Brussels'), ('Prague','Munich'), ('Riga','Munich'), ('Prague','Amsterdam'),
        ('Prague','Brussels'), ('Prague','Istanbul'), ('Istanbul','Stockholm'), ('Vienna','Prague'),
        ('Munich','Split'), ('Vienna','Amsterdam'), ('Prague','Stockholm'), ('Brussels','Seville'),
        ('Munich','Stockholm'), ('Istanbul','Brussels'), ('Amsterdam','Seville'), ('Vienna','Split'),
        ('Munich','Seville'), ('Riga','Brussels'), ('Prague','Riga'), ('Vienna','Munich')
    ]
    
    direct = set()
    for (a, b) in connections:
        direct.add((a, b))
        direct.add((b, a))
    
    s = Solver()
    
    CitySort, city_consts = EnumSort('City', Cities)
    city_map = {c: const for c, const in zip(Cities, city_consts)}
    
    base_city = [None]
    flight = [None]
    flight_to = [None]
    for d in range(1, 21):
        base_city.append(Const('base_city_%d' % d, CitySort))
        flight.append(Bool('flight_%d' % d))
        flight_to.append(Const('flight_to_%d' % d, CitySort))
    
    for d in range(1, 6):
        s.add(base_city[d] == city_map['Vienna'])
    s.add(flight[5] == True)
    s.add(flight_to[5] == city_map['Prague'])
    
    for d in range(6, 10):
        s.add(base_city[d] == city_map['Prague'])
    s.add(flight[9] == True)
    s.add(Or([flight_to[9] == city_map[c] for c in Cities if c not in ['Vienna', 'Prague']]))
    s.add(flight_to[9] != city_map['Vienna'])
    s.add(flight_to[9] != city_map['Prague'])
    
    s.add(flight[11] == True)
    s.add(flight_to[11] == city_map['Split'])
    
    s.add(flight[15] == True)
    s.add(flight_to[15] == city_map['Riga'])
    
    s.add(flight[16] == True)
    s.add(flight_to[16] == city_map['Stockholm'])
    
    for d in [1,2,3,4,6,7,8,12]:
        s.add(flight[d] == False)
    
    for d in range(1, 20):
        s.add(If(flight[d],
                 base_city[d+1] == flight_to[d],
                 base_city[d+1] == base_city[d]))
    
    for d in range(1, 20):
        or_conditions = []
        for (a, b) in direct:
            or_conditions.append(And(base_city[d] == city_map[a], flight_to[d] == city_map[b]))
        s.add(Implies(flight[d], Or(or_conditions)))
        s.add(Implies(flight[d], base_city[d] != flight_to[d]))
    
    counts = {c: 0 for c in Cities}
    for c in Cities:
        total = 0
        for d in range(1, 21):
            in_city = Or(base_city[d] == city_map[c], And(flight[d], flight_to[d] == city_map[c]))
            total += If(in_city, 1, 0)
        counts[c] = total
    
    s.add(counts['Vienna'] == 5)
    s.add(counts['Prague'] == 5)
    s.add(counts['Split'] == 3)
    s.add(counts['Riga'] == 2)
    s.add(counts['Stockholm'] == 2)
    s.add(counts['Brussels'] == 2)
    s.add(counts['Munich'] == 2)
    s.add(counts['Seville'] == 3)
    s.add(counts['Istanbul'] == 2)
    s.add(counts['Amsterdam'] == 3)
    
    for d in [5,6,7,8,9]:
        s.add(Or(base_city[d] == city_map['Prague'], And(flight[d], flight_to[d] == city_map['Prague'])))
    for d in [1,2,3,4,5]:
        s.add(Or(base_city[d] == city_map['Vienna'], And(flight[d], flight_to[d] == city_map['Vienna'])))
    for d in [15,16]:
        s.add(Or(base_city[d] == city_map['Riga'], And(flight[d], flight_to[d] == city_map['Riga'])))
    for d in [16,17]:
        s.add(Or(base_city[d] == city_map['Stockholm'], And(flight[d], flight_to[d] == city_map['Stockholm'])))
    for d in [11,12,13]:
        s.add(Or(base_city[d] == city_map['Split'], And(flight[d], flight_to[d] == city_map['Split'])))
    
    if s.check() == sat:
        m = s.model()
        base_city_names = [None] * 21
        flight_to_names = [None] * 21
        flight_flags = [None] * 21
        
        for d in range(1, 21):
            base_val = m.evaluate(base_city[d])
            base_name = None
            for c in Cities:
                if base_val.eq(city_map[c]):
                    base_name = c
                    break
            base_city_names[d] = base_name
            
            flight_val = m.evaluate(flight[d])
            flight_flags[d] = flight_val
            if flight_val:
                to_val = m.evaluate(flight_to[d])
                to_name = None
                for c in Cities:
                    if to_val.eq(city_map[c]):
                        to_name = c
                        break
                flight_to_names[d] = to_name
            else:
                flight_to_names[d] = None
        
        in_city_set = set()
        for d in range(1, 21):
            in_city_set.add((base_city_names[d], d))
            if flight_flags[d]:
                in_city_set.add((flight_to_names[d], d))
        
        city_days = {c: [] for c in Cities}
        for (c, d) in in_city_set:
            if c is not None:
                city_days[c].append(d)
        for c in Cities:
            city_days[c] = sorted(city_days[c])
        
        itinerary = []
        for c in Cities:
            if not city_days[c]:
                continue
            groups = []
            current = [city_days[c][0]]
            for i in range(1, len(city_days[c])):
                if city_days[c][i] == city_days[c][i-1] + 1:
                    current.append(city_days[c][i])
                else:
                    groups.append(current)
                    current = [city_days[c][i]]
            groups.append(current)
            
            for group in groups:
                start = group[0]
                end = group[-1]
                if start == end:
                    day_range_str = "Day %d" % start
                else:
                    day_range_str = "Day %d-%d" % (start, end)
                itinerary.append({"day_range": day_range_str, "place": c})
        
        for d in range(1, 20):
            if flight_flags[d] and flight_to_names[d] is not None and base_city_names[d] is not None:
                itinerary.append({"day_range": "Day %d" % d, "place": base_city_names[d]})
                itinerary.append({"day_range": "Day %d" % d, "place": flight_to_names[d]})
        
        def day_range_key(entry):
            parts = entry['day_range'].split()
            nums = parts[1]
            if '-' in nums:
                return int(nums.split('-')[0])
            else:
                return int(nums)
        
        itinerary.sort(key=day_range_key)
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()