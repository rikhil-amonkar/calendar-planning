from z3 import *
import json

def main():
    # Define the cities and their enum type
    Cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    CitySort, city_consts = EnumSort('City', Cities)
    man, stut, mad, vie = city_consts

    # Create sequence variables S0 to S15
    S = [Const(f'S_{i}', CitySort) for i in range(16)]
    
    # Define allowed direct flight pairs (both directions)
    allowed_pairs = [
        (vie, stut),
        (man, vie),
        (mad, vie),
        (man, stut),
        (man, mad)
    ]
    allowed_moves = set()
    for a, b in allowed_pairs:
        allowed_moves.add((a, b))
        allowed_moves.add((b, a))
    
    s = Solver()
    
    # Flight constraints: if moving between different cities, the move must be in allowed_moves
    for i in range(1, 16):
        a_prev = S[i-1]
        a_curr = S[i]
        move_condition = Or([And(a_prev == a, a_curr == b) for (a, b) in allowed_moves])
        s.add(If(a_prev != a_curr, move_condition, True))
    
    # Count days spent in each city
    man_days = 0
    stut_days = 0
    mad_days = 0
    vie_days = 0
    for i in range(1, 16):
        man_days += If(Or(S[i-1] == man, S[i] == man), 1, 0)
        stut_days += If(Or(S[i-1] == stut, S[i] == stut), 1, 0)
        mad_days += If(Or(S[i-1] == mad, S[i] == mad), 1, 0)
        vie_days += If(Or(S[i-1] == vie, S[i] == vie), 1, 0)
    
    s.add(man_days == 7)
    s.add(stut_days == 5)
    s.add(mad_days == 4)
    s.add(vie_days == 2)
    
    # Event constraints
    stut_event = Or([Or(S[i-1] == stut, S[i] == stut) for i in range(11, 16)])
    man_event = Or([Or(S[i-1] == man, S[i] == man) for i in range(1, 8)])
    s.add(stut_event)
    s.add(man_event)
    
    # Solve and output itinerary
    if s.check() == sat:
        m = s.model()
        city_names = {
            man: "Manchester",
            stut: "Stuttgart",
            mad: "Madrid",
            vie: "Vienna"
        }
        
        itinerary = []
        for day in range(1, 16):
            start_city = m[S[day-1]]
            end_city = m[S[day]]
            start_name = city_names.get(start_city, "Unknown")
            end_name = city_names.get(end_city, "Unknown")
            if start_name == end_name:
                place = start_name
            else:
                place = f"{start_name}, {end_name}"
            itinerary.append({"day": day, "place": place})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()