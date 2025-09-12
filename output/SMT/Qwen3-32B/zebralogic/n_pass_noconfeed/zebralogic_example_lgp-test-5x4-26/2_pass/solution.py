# Clue 12: brown hair (4) is left of mother Janelle (0)
solver.add(Or(
    And(hair_color[0] == 4, mother[1] == 0),
    And(hair_color[0] == 4, mother[2] == 0),
    And(hair_color[0] == 4, mother[3] == 0),
    And(hair_color[0] == 4, mother[4] == 0),
    And(hair_color[1] == 4, mother[2] == 0),
    And(hair_color[1] == 4, mother[3] == 0),
    And(hair_color[1] == 4, mother[4] == 0),
    And(hair_color[2] == 4, mother[3] == 0),
    And(hair_color[2] == 4, mother[4] == 0),
    And(hair_color[3] == 4, mother[4] == 0)
))