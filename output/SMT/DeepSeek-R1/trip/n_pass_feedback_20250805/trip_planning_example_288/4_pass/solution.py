from z3 import *
import json

def main():
    Cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    CitySort, (man, stut, mad, vie) = EnumSort('City', Cities)
    
    S = [Const(f'S_{i}', CitySort) for i in range(16)]
    
    allowed_pairs = [
        (vie, stut),
        (vie, man),
        (vie, mad),
        (man, stut),
        (man, mad)
    ]
    allowed_moves = set()
    for a, b in allowed_pairs:
        allowed_moves.add((a, b))
        allowed_moves.add((b, a))
    
    s = Solver()
    
    for i in range(1, 16):
        a_prev = S[i-1]
        a_curr = S[i]
        s.add(Or([And(a_prev == a, a_curr == b) for (a, b) in allowed_moves]))
    
    man_days = 0
    stut_days = 0
    mad_days = 0
    vie_days = 0
    travel_days = 0
    for i in range(1, 16):
        is_travel = If(S[i-1] != S[i], 1, 0)
        travel_days += is_travel
        man_days += If(Or(S[i-1] == man, S[i] == man), 1, 0)
        stut_days += If(Or(S[i-1] == stut, S[i] == stut), 1, 0)
        mad_days += If(Or(S[i-1] == mad, S[i] == mad), 1, 0)
        vie_days += If(Or(S[i-1] == vie, S[i] == vie), 1, 0)
    
    s.add(man_days == 7)
    s.add(stut_days == 5)
    s.add(mad_days == 4)
    s.add(vie_days == 2)
    s.add(travel_days == 3)
    
    man_event = Or([Or(S[i-1] == man, S[i] == man) for i in range(1, 8)])
    s.add(man_event)
    
    stut_event = Or([Or(S[i-1] == stut, S[i] == stut) for i in range(11, 16)])
    s.add(stut_event)
    
    if s.check() == sat:
        m = s.model()
        city_names = {
            man: "Manchester",
            stut: "Stuttgart",
            mad: "Madrid",
            vie: "Vienna"
        }
        
        per_day = []
        for day in range(1, 16):
            start_city = m[S[day-1]]
            end_city = m[S[day]]
            start_name = city_names[start_city]
            end_name = city_names[end_city]
            if start_name == end_name:
                place_str = start_name
            else:
                place_str = f"{start_name}, {end_name}"
            per_day.append(place_str)
        
        blocks = []
        start_index = 0
        current_place = per_day[0]
        for i in range(1, 15):
            if per_day[i] == current_place:
                continue
            else:
                end_index = i - 1
                if start_index == end_index:
                    day_range = f"Day {start_index+1}"
                else:
                    day_range = f"Day {start_index+1}-{end_index+1}"
                blocks.append({'day_range': day_range, 'place': current_place})
                start_index = i
                current_place = per_day[i]
        if start_index < 15:
            end_index = 14
            if start_index == end_index:
                day_range = f"Day {start_index+1}"
            else:
                day_range = f"Day {start_index+1}-{end_index+1}"
            blocks.append({'day_range': day_range, 'place': current_place})
        
        result = {'itinerary': blocks}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()