
// TODO use auto contract for every method!

class {:autocontracts} CarPark {

    var reservedSpace: set<int>;    // Set for lots that have been reserved
    
    var generalSpace: set<int>;     // Set for ltos that dont have a reservation on them
    
    var maxSpace: int;              // Maximum number of cars in overall 

    var spacesAvailable: int;       // Number of spaces available
    
    var maxReservedSpace: int;      // Number of reserved spaces available

    var maxGeneralSpace: int;

    var carsWRes: set<int>;         // Set of cars that have a active reservation
    
    var parkingRestriction: bool;   // Boolean for parking restriction
    


    // a constructor for the class, setting the car-park up for a new day.
    //x -> size of carpark
    //y -> size of reservedSpace
    constructor (x: int, y: int)
    requires x - 8 > y
    requires 0 < x - 8     //requires that the size of the carPark must be greater than 8
    requires 0 <= y
    {
        maxSpace := x;
        maxReservedSpace := y;
        parkingRestriction := true;
        spacesAvailable := x - 8;
        maxGeneralSpace := x - 8 - y;

        reservedSpace := {};
        generalSpace := {};
    }

    // to allow any car without a reservation to enter the car park.
    method enterCarPark (x: int) returns (res: bool)
    //ensures that car is either in generalSpace or reservedSpace after correct execution
    ensures res ==> x in generalSpace || x in reservedSpace
    //ensures that the sum of the carpark is 1 larger after the method executes correctly
    ensures res ==> |generalSpace|+|reservedSpace| == old(|generalSpace|)+old(|reservedSpace|) + 1
    //ensures that the reservedSpace carPark was not touched
    ensures old(reservedSpace) == reservedSpace || old(generalSpace) == generalSpace
    modifies this;
    {
        //check if there is free space availalbe
        if(spacesAvailable > 0 && maxSpace > |generalSpace| + |reservedSpace|) {
            //check that car does not exist in carparks 
            if !(x in generalSpace) && !(x in reservedSpace){
                //decide where to put the car
                if(|generalSpace| < maxGeneralSpace) {
                    generalSpace := generalSpace + {x};
                    spacesAvailable := spacesAvailable - 1;
                    res := true; 
                    print "[S] Car {",x,"} parked in general space", "\n";
                } else if (|reservedSpace| < maxReservedSpace && parkingRestriction) {
                    print "[S] Car {",x,"} parked in reserved space", "\n";
                    spacesAvailable := spacesAvailable - 1;
                    reservedSpace := reservedSpace + {x};
                    res := true;
                } else {
                    print "[F] Car {",x,"} not admitted in general space","\n";
                    res := false;
                }
            } else {
                print "[F] Car {",x,"} not admitted in general space","\n";
                res := false;
            }

        } else {
            print "[F] Car {",x,"} not admitted in general space","\n";
            res := false;
        } 
    }

    // to allow any car from any area to leave the car park.
    // x is the id of the car
    method leaveCarPark(x: int) returns (res: bool)
    // ensures that car is not in the sets anymore
    ensures res ==> !(x in generalSpace) || !(x in reservedSpace);
    modifies this;
    {
        if(x in generalSpace) {
            generalSpace := generalSpace - {x};
            spacesAvailable := spacesAvailable + 1;
            res:= true;
        } else if (x in reservedSpace) {
            reservedSpace := reservedSpace - {x};
            spacesAvailable := spacesAvailable + 1;
            res := true;
        } else {
            res := false;
        }
    }

    // to report on the number of non-reserved free spaces currently available.
    method checkAvailability () returns (res: int)
    requires true;
    ensures old(generalSpace) == generalSpace;
    ensures old(reservedSpace) == reservedSpace;
    {
        res := maxSpace - |generalSpace| - |reservedSpace| - 8;
    }
    
    // to allow a car with a reservation to enter the car park’s reserved area during its hours of operation, or to enter the car park generally outside these hours.
    method enterReservedCarPark (x: int) returns (res: bool)
    ensures res ==> old(reservedSpace) + old(generalSpace) + {x} == reservedSpace + generalSpace
    ensures res ==> old(reservedSpace) == reservedSpace || old(generalSpace) == generalSpace 
    modifies this;
    {
        if(spacesAvailable > 0) {
            if(x in carsWRes && maxSpace > |generalSpace| + |reservedSpace|) {
                if(|reservedSpace| < maxReservedSpace) {
                    spacesAvailable := spacesAvailable - 1;
                    reservedSpace :=  reservedSpace + {x};
                    print "[S] Car {",x,"} with valid subscription parked in reserved space\n";
                } else {
                    generalSpace := generalSpace + {x};
                    spacesAvailable := spacesAvailable - 1;
                    print "[S] Car {",x,"} parked in general space\n";
                }
                res := true;
            } else {
                print "[F] Car {",x,"} has not been parked in reserved area\n";
                res := false;
            }
        } else {
            print "[F] Car {",x,"} has not been parked in reserved area\n";
            res := false;
            
        }
 
    }
    
    // to allow a car to be registered as having a reserved space when the owner pays the subscription.
    method makeSubscription (x: int) returns (res: bool)
    modifies this;
    ensures old(generalSpace) == generalSpace && old(reservedSpace) == reservedSpace
    {
        if(!(x in generalSpace || x in reservedSpace) && (|carsWRes| < maxSpace - 8) && !(x in carsWRes)){
            carsWRes := carsWRes + {x};
            print "[S] Car {",x,"} has been added to subscription list","\n";
            res := true;
        } else {
            print "[F] Car {",x,"} has not been added to subscription list","\n";
            res := false;
        }

    }

    // to remove parking restrictions on the reserved spaces (i.e. at 3pm).
    method openReservedArea() returns ()
    ensures old(generalSpace) == generalSpace;
    ensures old(reservedSpace) == reservedSpace;
    ensures old(carsWRes) == carsWRes;
    ensures old(maxSpace) == maxSpace;
    modifies this;
    {
        parkingRestriction := false;
    }

    // to remove and crush remaining parked cars at closing time.
    method closeCarPark() returns ()
    ensures |generalSpace| == 0 && |reservedSpace| == 0;
    ensures carsWRes == old(carsWRes)
    modifies this;
    {
        generalSpace := {};
        reservedSpace := {};
        spacesAvailable := maxSpace - 8;
    }

    predicate Valid()
    reads this;
    {
        maxSpace > 8 &&
        maxSpace == maxGeneralSpace+ maxReservedSpace + 8 &&
        maxSpace >= |generalSpace| + |reservedSpace| &&
        spacesAvailable >= 0 &&
        |reservedSpace| <= maxReservedSpace &&
        |generalSpace| >= 0 && |reservedSpace| >= 0
    }
    method printStats() returns ()
    requires true
    ensures old(generalSpace) == generalSpace;
    ensures old(reservedSpace) == reservedSpace;
    ensures old(carsWRes) == carsWRes;
    ensures old(maxSpace) == maxSpace;
    {
        var a := generalSpace;
        var b := reservedSpace;
        var c := carsWRes;
        var s := spacesAvailable;
        print "\n", "##### CAR PARK REPORT #####", "\n";
        print "Free Space", " (", spacesAvailable," of " , maxSpace, ")", "\n";

        while ( s != 0 && 0 < s)
            decreases s;
            {
                print "[ ]", " ";
                s := s - 1;
            }
        
        

        print "\n", "\n", "General Space", " (", |generalSpace|," of " , maxGeneralSpace, ")", "\n";
        while ( a != {} )
        decreases a;
        {
            var y :| y in a;
            print "[", y, "]", " ";
            a := a - { y };
        }

        print "\n", "\n", "Reserved Space", " (", |reservedSpace|," of " , maxReservedSpace, ")", "\n";
        while ( b != {} )
        decreases b;
        {
            var y :| y in b;
            print "[", y, "]", " ";
            b := b - { y };
        }

        print "\n","\n", "Reservations", "\n";
        while ( c != {} )
        decreases c;
        {
            var y :| y in c;
            print y, ", ";
            c := c - { y };
        }
    }
}
method Main ()  
{
    var cp := new CarPark(15, 3);
    var b1 := cp.makeSubscription(1);
        
    print "-- Testing duplicate subscription","\n","-- ";
    var b2 := cp.makeSubscription(1);

    var b6 := cp.makeSubscription(6);

    var b3 := cp.enterCarPark(2);
    var b31 := cp.enterCarPark(3);
    var b311 := cp.leaveCarPark(3);
    var b32 := cp.enterCarPark(4);

    print "-- Testing parking without subscription","\n","-- ";
    var b5 := cp.enterReservedCarPark(5);

    var b4 := cp.enterReservedCarPark(1);
    var b61 := cp.enterCarPark(6);
    var b7 := cp.enterCarPark(7);
    var b8 := cp.enterCarPark(8);
    var b9 := cp.enterCarPark(9);
    
    cp.printStats();

    print "\n", "\n", "#### Opening Reserved Area ####", "\n", "\n";
    cp.openReservedArea();

    print "-- Testing general parking while carpark is full","\n","-- ";
    var b10 := cp.enterReservedCarPark(10);
    print "-- Testing reserved parking while carpark is full","\n","-- ";
    var b11 := cp.enterCarPark(11);
    
    cp.printStats();
    
    print "\n", "\n", "#### Closing Car Park ####", "\n", "\n";
    cp.closeCarPark();

    cp.printStats();
}
