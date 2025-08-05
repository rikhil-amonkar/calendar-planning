from z3 import *
import json

def main():
    # Define the cities
    City, (AMS, EDI, BRU, VIE, BER, REK) = EnumSort('City', ['AMS', 'EDI', 'BRU', 'VIE', 'BER', 'REK'])
    cities = [AMS, EDI, BRU, VIE, BER, REK]
    city_names = {
        AMS: 'Amsterdam',
        EDI: 'Edinburgh',
        BRU: 'Brussels',
        VIE: 'Vienna',
        BER: 'Berlin',
        REK: 'Reykjavik'
    }
    
    # Required days per city
    required_days = {
        AMS: 4,
        EDI: 5,
        BRU: 5,
        VIE: 5,
        BER: 4,
        REK: 5
    }
    
    # Direct flights (both directions)
    direct_flights = [
        (EDI, BER), (AMS, BER), (EDI, AMS), (VIE, BER), (BER, BRU),
        (VIE, REK), (EDI, BRU), (VIE, BRU), (AMS, REK), (REK, BRU),
        (AMS, VIE), (REK, BER)
    ]
    allowed_pairs = []
    for (a, b) in direct_flights:
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))
    
    n_days = 23
    c = [Const('c_%d' % i, City) for i in range(n_days)]
    s = Solver()
    
    # Flight constraints: consecutive days must be same city or direct flight
    for i in range(n_days - 1):
        same_city = c[i] == c[i + 1]
        valid_flight = Or([And(c[i] == a, c[i + 1] == b) for (a, b) in allowed_pairs])
        s.add(Or(same_city, valid_flight))
    
    # Total days per city (including flight days)
    total_days = {}
    for city in cities:
        in_city_list = []
        for j in range(n_days):
            # Day j: either stayed in city or flew to city from another city
            stayed = (c[j] == city)
            flew_in = And(j < n_days - 1, c[j + 1] == city, c[j] != city)
            in_city = Or(stayed, flew_in)
            in_city_list.append(in_city)
        total_days[city] = Sum([If(cond, 1, 0) for cond in in_city_list])
        s.add(total_days[city] == required_days[city])
    
    # Specific date constraints
    # Amsterdam between day 5 and 8 (days 5,6,7,8 -> indices 4,5,6,7)
    ams_days = []
    for idx in [4,5,6,7]:
        stayed = (c[idx] == AMS)
        flew_in = And(idx < n_days - 1, c[idx + 1] == AMS, c[idx] != AMS)
        ams_days.append(Or(stayed, flew_in))
    s.add(Or(ams_days))
    
    # Berlin between day 16 and 19 (days 16,17,18,19 -> indices 15,16,17,18)
    ber_days = []
    for idx in [15,16,17,18]:
        stayed = (c[idx] == BER)
        flew_in = And(idx < n_days - 1, c[idx + 1] == BER, c[idx] != BER)
        ber_days.append(Or(stayed, flew_in))
    s.add(Or(ber_days))
    
    # Reykjavik between day 12 and 16 (days 12,13,14,15,16 -> indices 11,12,13,14,15)
    rek_days = []
    for idx in [11,12,13,14,15]:
        stayed = (c[idx] == REK)
        flew_in = And(idx < n_days - 1, c[idx + 1] == REK, c[idx] != REK)
        rek_days.append(Or(stayed, flew_in))
    s.add(Or(rek_days))
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for i in range(n_days):
            city_val = m.eval(c[i])
            itinerary_list.append({"day": i + 1, "place": city_names[city_val]})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()