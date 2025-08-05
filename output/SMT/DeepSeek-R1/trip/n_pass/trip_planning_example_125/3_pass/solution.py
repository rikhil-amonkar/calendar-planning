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
    
    s = Solver()
    
    start_city = [Int('start_%d' % i) for i in range(15)]
    end_city = [Int('end_%d' % i) for i in range(15)]
    
    for i in range(15):
        s.add(Or(start_city[i] == stuttgart, start_city[i] == seville, start_city[i] == manchester))
        s.add(Or(end_city[i] == stuttgart, end_city[i] == seville, end_city[i] == manchester))
    
    for i in range(14):
        s.add(end_city[i] == start_city[i+1])
    
    for i in range(15):
        same_city = (start_city[i] == end_city[i])
        stut_to_man = And(start_city[i] == stuttgart, end_city[i] == manchester)
        man_to_stut = And(start_city[i] == manchester, end_city[i] == stuttgart)
        man_to_sev = And(start_city[i] == manchester, end_city[i] == seville)
        sev_to_man = And(start_city[i] == seville, end_city[i] == manchester)
        s.add(Or(same_city, stut_to_man, man_to_stut, man_to_sev, sev_to_man))
    
    stuttgart_count = 0
    seville_count = 0
    manchester_count = 0
    
    for i in range(15):
        stuttgart_count += If(Or(start_city[i] == stuttgart, 
                                 And(end_city[i] == stuttgart, start_city[i] != stuttgart)), 1, 0)
        seville_count += If(Or(start_city[i] == seville, 
                               And(end_city[i] == seville, start_city[i] != seville)), 1, 0)
        manchester_count += If(Or(start_city[i] == manchester, 
                                  And(end_city[i] == manchester, start_city[i] != manchester)), 1, 0)
    
    s.add(stuttgart_count == 6)
    s.add(seville_count == 7)
    s.add(manchester_count == 4)
    
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