from z3 import *

def main():
    flights = [
        {'flight_time': 0, 'priority': 1, 'flight_id': 'flight1'},
        {'flight_time': 0, 'priority': 1, 'flight_id': 'flight2'}
    ]
    
    req = {
        0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 7: 0, 8: 0, 9: 0,
        10: 0, 11: 0, 12: 0, 13: 0, 14: 0, 15: 0, 16: 0, 17: 0, 18: 0, 19: 0,
        20: 0, 21: 0, 22: 0, 23: 0, 24: 0, 25: 0, 26: 0, 27: 0, 28: 0, 29: 0,
        30: 0, 31: 0, 32: 0, 33: 0, 34: 0, 35: 0, 36: 0, 37: 0, 38: 0, 39: 0,
        40: 0, 41: 0, 42: 0, 43: 0, 44: 0, 45: 0, 46: 0, 47: 0, 48: 0, 49: 0,
        50: 0, 51: 0, 52: 0, 53: 0, 54: 0, 55: 0, 56: 0, 57: 0, 58: 0, 59: 0,
        60: 0, 61: 0, 62: 0, 63: 0, 64: 0, 65: 0, 66: 0, 67: 0, 68: 0, 69: 0,
        70: 0, 71: 0, 72: 0, 73: 0, 74: 0, 75: 0, 76: 0, 77: 0, 78: 0, 79: 0,
        80: 0, 81: 0, 82: 0, 83: 0, 84: 0, 85: 0, 86: 0, 87: 0, 88: 0, 89: 0,
        90: 0, 91: 0, 92: 0, 93: 0, 94: 0, 95: 0, 96: 0, 97: 0, 98: 0, 99: 0
    }
    
    # Use Optimize instead of Solver for maximization
    opt = Optimize()
    
    # Create Z3 array for required times
    required_arr = Array('required_arr', IntSort(), IntSort())
    for i in range(100):
        opt.add(required_arr[i] == req[i])
    
    # Extract flight data
    f1 = flights[0]['flight_time']
    p1 = flights[0]['priority']
    id1 = flights[0]['flight_id']
    
    f2 = flights[1]['flight_time']
    p2 = flights[1]['priority']
    id2 = flights[1]['flight_id']
    
    # Create variables
    scheduled1 = Bool('scheduled1')
    scheduled2 = Bool('scheduled2')
    block1 = Int('block1')
    block2 = Int('block2')
    
    # Total priority expression
    total_priority = If(scheduled1, p1, 0) + If(scheduled2, p2, 0)
    
    # Constraints for flight1
    opt.add(Implies(scheduled1, And(block1 >= 0, block1 < 100, required_arr[block1] >= f1)))
    
    # Constraints for flight2
    opt.add(Implies(scheduled2, And(block2 >= 0, block2 < 100, required_arr[block2] >= f2)))
    
    # Non-overlapping constraint
    opt.add(Implies(And(scheduled1, scheduled2), block1 != block2))
    
    # Maximize total priority
    opt.maximize(total_priority)
    
    # Solve and output
    if opt.check() == sat:
        m = opt.model()
        scheduled_flights = []
        if is_true(m.eval(scheduled1)):
            scheduled_flights.append({'flight_id': id1, 'block': m.eval(block1).as_long()})
        if is_true(m.eval(scheduled2)):
            scheduled_flights.append({'flight_id': id2, 'block': m.eval(block2).as_long()})
        total_pri = m.eval(total_priority).as_long()
        result = {
            'scheduled_flights': scheduled_flights,
            'total_priority': total_pri
        }
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()