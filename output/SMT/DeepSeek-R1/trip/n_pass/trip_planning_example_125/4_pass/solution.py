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
    
    stuttgart_count = Sum([If(Or(start_city[i] == stuttgart, end_city[i] == stuttgart), 1, 0) for i in range(15)])
    seville_count = Sum([If(Or(start_city[i] == seville, end_city[i] == seville), 1, 0) for i in range(15)])
    manchester_count = Sum([If(Or(start_city[i] == manchester, end_city[i] == manchester), 1, 0) for i in range(15)])
    
    s.add(stuttgart_count == 6)
    s.add(seville_count == 7)
    s.add(manchester_count == 4)
    
    meeting_constraint = Or([Or(start_city[i] == stuttgart, end_city[i] == stuttgart) for i in range(6)])
    s.add(meeting_constraint)
    
    if s.check() == sat:
        model = s.model()
        days = []
        for i in range(15):
            end_val = model.eval(end_city[i]).as_long()
            days.append(end_val)
        
        itinerary = []
        current_city = days[0]
        start_day = 1
        end_day = 1
        for i in range(1, 15):
            if days[i] == current_city:
                end_day = i + 1
            else:
                if start_day == end_day:
                    day_range = "Day %d" % start_day
                else:
                    day_range = "Day %d-%d" % (start_day, end_day)
                itinerary.append({'day_range': day_range, 'place': city_names[current_city]})
                current_city = days[i]
                start_day = i + 1
                end_day = i + 1
        
        if start_day == end_day:
            day_range = "Day %d" % start_day
        else:
            day_range = "Day %d-%d" % (start_day, end_day)
        itinerary.append({'day_range': day_range, 'place': city_names[current_city]})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No valid itinerary found.")

if __name__ == '__main__':
    main()