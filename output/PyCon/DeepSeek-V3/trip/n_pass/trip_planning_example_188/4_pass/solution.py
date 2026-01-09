import json
from constraint import Problem

def solve_itinerary():
    # Problem parameters
    total_days = 12
    brussels_days = 2
    split_days = 5
    barcelona_days = 7
    
    # Create constraint problem
    problem = Problem()
    
    # Define variables: start days for each city stay
    problem.addVariable("brussels_start", range(1, total_days + 1))
    problem.addVariable("barcelona_start", range(1, total_days + 1))
    problem.addVariable("split_start", range(1, total_days + 1))
    
    # Constraint: Brussels must start on day 1 (conference requirement)
    problem.addConstraint(lambda bs: bs == 1, ["brussels_start"])
    
    # Constraint: All stays must fit within the 12-day period
    problem.addConstraint(lambda bs: bs + brussels_days - 1 <= total_days, ["brussels_start"])
    problem.addConstraint(lambda bcn: bcn + barcelona_days - 1 <= total_days, ["barcelona_start"])
    problem.addConstraint(lambda ss: ss + split_days - 1 <= total_days, ["split_start"])
    
    # Constraint: No overlapping stays
    def no_overlap(bs, bcn, ss):
        brussels_end = bs + brussels_days - 1
        barcelona_end = bcn + barcelona_days - 1
        split_end = ss + split_days - 1
        
        # Check if any two stays overlap
        brussels_barcelona_overlap = (bs <= barcelona_end and bcn <= brussels_end)
        brussels_split_overlap = (bs <= split_end and ss <= brussels_end)
        barcelona_split_overlap = (bcn <= split_end and ss <= barcelona_end)
        
        return not (brussels_barcelona_overlap or brussels_split_overlap or barcelona_split_overlap)
    
    problem.addConstraint(no_overlap, ["brussels_start", "barcelona_start", "split_start"])
    
    # Constraint: Flight connectivity - Brussels connects only to Barcelona, Barcelona connects to Split
    # Valid sequence must be: Brussels -> Barcelona -> Split
    def valid_flight_sequence(bs, bcn, ss):
        brussels_end = bs + brussels_days - 1
        barcelona_end = bcn + barcelona_days - 1
        
        # Brussels must be first, then Barcelona, then Split
        # Brussels ends before Barcelona starts (Brussels -> Barcelona)
        # Barcelona ends before Split starts (Barcelona -> Split)
        return (brussels_end + 1 == bcn) and (barcelona_end + 1 == ss)
    
    problem.addConstraint(valid_flight_sequence, ["brussels_start", "barcelona_start", "split_start"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    bs = solution["brussels_start"]
    bcn = solution["barcelona_start"]
    ss = solution["split_start"]
    
    brussels_end = bs + brussels_days - 1
    barcelona_end = bcn + barcelona_days - 1
    split_end = ss + split_days - 1
    
    # Create itinerary segments
    itinerary = []
    
    # Add Brussels segment
    itinerary.append({"day_range": f"Day {bs}-{brussels_end}", "place": "Brussels"})
    
    # Add Barcelona segment  
    itinerary.append({"day_range": f"Day {bcn}-{barcelona_end}", "place": "Barcelona"})
    
    # Add Split segment
    itinerary.append({"day_range": f"Day {ss}-{split_end}", "place": "Split"})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))