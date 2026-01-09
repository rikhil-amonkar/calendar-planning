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
    problem.addVariable("split_start", range(1, total_days + 1))
    problem.addVariable("barcelona_start", range(1, total_days + 1))
    
    # Constraint: Brussels must start on day 1 (conference requirement)
    problem.addConstraint(lambda bs: bs == 1, ["brussels_start"])
    
    # Constraint: All stays must fit within the 12-day period
    problem.addConstraint(lambda bs: bs + brussels_days - 1 <= total_days, ["brussels_start"])
    problem.addConstraint(lambda ss: ss + split_days - 1 <= total_days, ["split_start"])
    problem.addConstraint(lambda bcn: bcn + barcelona_days - 1 <= total_days, ["barcelona_start"])
    
    # Constraint: No overlapping stays
    def no_overlap(bs, ss, bcn):
        brussels_end = bs + brussels_days - 1
        split_end = ss + split_days - 1
        barcelona_end = bcn + barcelona_days - 1
        
        # Check if any two stays overlap
        brussels_split_overlap = (bs <= split_end and ss <= brussels_end)
        brussels_barcelona_overlap = (bs <= barcelona_end and bcn <= brussels_end)
        split_barcelona_overlap = (ss <= barcelona_end and bcn <= split_end)
        
        return not (brussels_split_overlap or brussels_barcelona_overlap or split_barcelona_overlap)
    
    problem.addConstraint(no_overlap, ["brussels_start", "split_start", "barcelona_start"])
    
    # Constraint: Flight connectivity - Brussels connects only to Barcelona, Barcelona connects to Split
    # This means the sequence must be Brussels -> Barcelona -> Split
    def valid_sequence(bs, ss, bcn):
        brussels_end = bs + brussels_days - 1
        barcelona_end = bcn + barcelona_days - 1
        
        # Brussels must end before Barcelona starts
        # Barcelona must end before Split starts
        return (brussels_end < bcn) and (barcelona_end < ss)
    
    problem.addConstraint(valid_sequence, ["brussels_start", "split_start", "barcelona_start"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    bs = solution["brussels_start"]
    ss = solution["split_start"]
    bcn = solution["barcelona_start"]
    
    brussels_end = bs + brussels_days - 1
    split_end = ss + split_days - 1
    barcelona_end = bcn + barcelona_days - 1
    
    # Create itinerary segments
    itinerary = []
    
    # Add Brussels segment
    itinerary.append({"day_range": f"Day {bs}-{brussels_end}", "place": "Brussels"})
    
    # Add Barcelona segment
    itinerary.append({"day_range": f"Day {bcn}-{barcelona_end}", "place": "Barcelona"})
    
    # Add Split segment
    itinerary.append({"day_range": f"Day {ss}-{split_end}", "place": "Split"})
    
    # Sort itinerary by start day (should already be in order due to constraints)
    itinerary.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))