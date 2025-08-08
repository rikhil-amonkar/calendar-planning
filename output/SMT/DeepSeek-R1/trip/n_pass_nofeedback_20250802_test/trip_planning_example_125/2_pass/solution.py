from z3 import *

def main():
    stuttgart = 0
    seville = 1
    manchester = 2
    city_names = {
        stuttgart: 'Stuttgart',
        seville: 'Seville',
        manchester: 'Manchester'
    }
    
    # Create arrays for start and end cities for 15 days
    start_city = [Int('start_%d' % i) for i in range(15)]
    end_city = [Int('end_%d' % i) for i in range(15)]
    
    s = Solver()
    
    # Each city variable must be 0, 1, or 2
    for i in range(15):
        s.add(Or(start_city[i] == stuttgart, start_city[i] == seville, start_city[i] == manchester))
        s.add(Or(end_city[i] == stuttgart, end_city[i] == seville, end_city[i] == manchester))
    
    # Chain constraint: end city of day i must equal start city of day i+1
    for i in range(14):
        s.add(end_city[i] == start_city[i+1])
    
    # Flight constraints: either stay in the same city or take a direct flight
    for i in range(15):
        same_city = (start_city[i] == end_city[i])
        man_to_sev = And(start_city[i] == manchester, end_city[i] == seville)
        sev_to_man = And(start_city[i] == seville, end_city[i] == manchester)
        stut_to_man = And(start_city[i] == stuttgart, end_city[i] == manchester)
        man_to_stut = And(start_city[i] == manchester, end_city[i] == stuttgart)
        s.add(Or(same_city, man_to_sev, sev_to_man, stut_to_man, man_to_stut))
    
    # Start in Stuttgart to satisfy meeting constraint early
    s.add(start_city[0] == stuttgart)
    
    # Count for Stuttgart
    stuttgart_count = 0
    for i in range(15):
        stuttgart_count += If(start_city[i] == stuttgart, 1, 0)
        stuttgart_count += If(And(end_city[i] == stuttgart, start_city[i] != stuttgart), 1, 0)
    s.add(stuttgart_count == 6)
    
    # Count for Seville
    seville_count = 0
    for i in range(15):
        seville_count += If(start_city[i] == seville, 1, 0)
        seville_count += If(And(end_city[i] == seville, start_city[i] != seville), 1, 0)
    s.add(seville_count == 7)
    
    # Count for Manchester
    manchester_count = 0
    for i in range(15):
        manchester_count += If(start_city[i] == manchester, 1, 0)
        manchester_count += If(And(end_city[i] == manchester, start_city[i] != manchester), 1, 0)
    s.add(manchester_count == 4)
    
    # Meeting constraint: must be in Stuttgart on at least one of the first 6 days (days 1-6)
    meeting_constraint = Or([Or(start_city[i] == stuttgart, end_city[i] == stuttgart) for i in range(6)])
    s.add(meeting_constraint)
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(15):
            end_val = model[end_city[i]].as_long()
            city_name = city_names[end_val]
            itinerary.append({"day": i+1, "place": city_name})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No valid itinerary found.")

if __name__ == '__main__':
    main()