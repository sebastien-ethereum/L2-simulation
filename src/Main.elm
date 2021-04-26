port module Main exposing (..)

import Browser
import Html exposing (..)
import Html.Attributes exposing (..)
import Html.Events exposing (..)


type Formula
    = Shift Formula
    | Mul2 Formula Formula
    | Mul0
    | Add2 Formula Formula
    | Add0


type Bias
    = Bias_Shift
    | Bias_Mul2L Bias
    | Bias_Mul2R Bias
    | Bias_Add2L Bias
    | Bias_Add2R Bias


type alias Locus =
    List Bias


type Pattern
    = Pattern_Shift
    | Pattern_Mul2 Pattern Pattern
    | Pattern_Mul0
    | Pattern_Add2L Pattern
    | Pattern_Add2R Pattern


type alias Action =
    ( Locus, Pattern )


type alias Dispute =
    List Action


polarity : Locus -> Bool
polarity s =
    modBy 2 (List.length s) == 0


subformula : Locus -> Formula -> Maybe Formula
subformula s a =
    case s of
        [] ->
            Just a

        i :: t ->
            case ( i, a ) of
                ( Bias_Shift, Shift b ) ->
                    subformula t b

                ( Bias_Mul2L j, Mul2 b _ ) ->
                    subformula (j :: t) b

                ( Bias_Mul2R j, Mul2 _ b ) ->
                    subformula (j :: t) b

                ( Bias_Add2L j, Add2 b _ ) ->
                    subformula (j :: t) b

                ( Bias_Add2R j, Add2 _ b ) ->
                    subformula (j :: t) b

                _ ->
                    Nothing


isPatternFor : Pattern -> Formula -> Bool
isPatternFor p a =
    case ( p, a ) of
        ( Pattern_Shift, Shift _ ) ->
            True

        ( Pattern_Mul2 q r, Mul2 b c ) ->
            isPatternFor q b && isPatternFor r c

        ( Pattern_Mul0, Mul0 ) ->
            True

        ( Pattern_Add2L q, Add2 b _ ) ->
            isPatternFor q b

        ( Pattern_Add2R q, Add2 _ b ) ->
            isPatternFor q b

        _ ->
            False


ramification : Pattern -> List Bias
ramification p =
    case p of
        Pattern_Shift ->
            [ Bias_Shift ]

        Pattern_Mul2 q r ->
            List.map Bias_Mul2L (ramification q) ++ List.map Bias_Mul2R (ramification r)

        Pattern_Mul0 ->
            []

        Pattern_Add2L q ->
            List.map Bias_Add2L (ramification q)

        Pattern_Add2R q ->
            List.map Bias_Add2R (ramification q)


isInitial : Action -> Formula -> Bool
isInitial ( t, q ) a =
    case listUnsnoc t of
        Nothing ->
            isPatternFor q a

        Just _ ->
            False


isJustifiedBy : Action -> Action -> Formula -> Bool
isJustifiedBy ( t, q ) ( s, p ) a =
    case listUnsnoc t of
        Nothing ->
            False

        Just ( u, i ) ->
            List.all identity
                [ u == s
                , List.member i (ramification p)
                , case subformula t a of
                    Just b ->
                        isPatternFor q b

                    Nothing ->
                        False
                ]


justifyingPrefix : Dispute -> Action -> Formula -> Maybe Dispute
justifyingPrefix d m a =
    case listUnsnoc d of
        Nothing ->
            if isInitial m a then
                Just d

            else
                Nothing

        Just ( e, n ) ->
            if isJustifiedBy m n a then
                Just d

            else
                justifyingPrefix e m a


chronicle : Dispute -> Formula -> Dispute
chronicle d a =
    case listUnsnoc d of
        Nothing ->
            []

        Just ( e, m ) ->
            case justifyingPrefix e m a of
                Just f ->
                    chronicleOp f a ++ [ m ]

                Nothing ->
                    Debug.todo "illegal"


chronicleOp : Dispute -> Formula -> Dispute
chronicleOp d a =
    case listUnsnoc d of
        Nothing ->
            []

        Just ( e, m ) ->
            chronicle e a ++ [ m ]


isJustified : Action -> Dispute -> Formula -> Bool
isJustified m d a =
    case justifyingPrefix (chronicle d a) m a of
        Just _ ->
            True

        Nothing ->
            False


isAffine : Action -> Dispute -> Formula -> Bool
isAffine (( t, _ ) as m) d a =
    case d of
        [] ->
            True

        ( s, _ ) :: e ->
            if s == t then
                False

            else
                isAffine m e a


isLegal : Action -> Dispute -> Formula -> Bool
isLegal m d a =
    List.all identity
        [ isJustified m d a
        , isAffine m d a
        ]


initialDispute : Dispute
initialDispute =
    []


advanceDispute : Action -> Dispute -> Formula -> Maybe Dispute
advanceDispute m d a =
    if isLegal m d a then
        Just (d ++ [ m ])

    else
        Nothing



--


type alias Agent =
    { principal : Maybe Locus
    , auxiliary : List Locus
    }


type alias Net =
    { active : Agent
    , passive : List Agent
    }


getAgent : Locus -> Net -> Agent
getAgent s net =
    case List.filter (\agent -> agent.principal == Just s) net.passive of
        [ agent ] ->
            agent

        _ ->
            Agent Nothing []


initialNet : Net
initialNet =
    { active =
        { principal = Nothing
        , auxiliary = [ [] ]
        }
    , passive =
        [ { principal = Just []
          , auxiliary = []
          }
        ]
    }


advanceNet : Action -> Net -> Net
advanceNet ( s, p ) net =
    let
        children =
            List.map
                (\i ->
                    { principal = Just (s ++ [ i ])
                    , auxiliary = List.filter ((/=) s) net.active.auxiliary
                    }
                )
                (ramification p)

        newActive =
            let
                agent =
                    getAgent s net
            in
            { agent | auxiliary = agent.auxiliary ++ List.filterMap .principal children }

        newPassive =
            net.passive
                |> List.filter (\agent -> agent.principal /= Just s)
                |> List.map (\agent -> { agent | auxiliary = List.filter ((/=) s) agent.auxiliary })
                |> List.append children
    in
    { net
        | active = newActive
        , passive = newPassive
    }


disputeToNet : Dispute -> Net
disputeToNet =
    List.foldl advanceNet initialNet


dotLocus : Locus -> String
dotLocus =
    dotLocus_ False


dotLocus_ : Bool -> Locus -> String
dotLocus_ parenthesize s =
    let
        leftParen =
            if parenthesize then
                "("

            else
                ""

        rightParen =
            if parenthesize then
                ")"

            else
                ""
    in
    String.concat
        [ case s of
            [] ->
                String.concat
                    [ here ]

            Bias_Shift :: t ->
                String.concat
                    [ leftParen
                    , posShift
                    , dotLocusOp_ True t
                    , rightParen
                    ]

            (Bias_Mul2L j) :: t ->
                String.concat
                    [ leftParen
                    , dotLocus_ True (j :: t)
                    , posMul2
                    , hole
                    , rightParen
                    ]

            (Bias_Mul2R j) :: t ->
                String.concat
                    [ leftParen
                    , hole
                    , posMul2
                    , dotLocus_ True (j :: t)
                    , rightParen
                    ]

            (Bias_Add2L j) :: t ->
                String.concat
                    [ leftParen
                    , dotLocus_ True (j :: t)
                    , posAdd2
                    , hole
                    , rightParen
                    ]

            (Bias_Add2R j) :: t ->
                String.concat
                    [ leftParen
                    , hole
                    , posAdd2
                    , dotLocus_ True (j :: t)
                    , rightParen
                    ]
        ]


dotLocusOp_ : Bool -> Locus -> String
dotLocusOp_ parenthesize s =
    let
        leftParen =
            if parenthesize then
                "("

            else
                ""

        rightParen =
            if parenthesize then
                ")"

            else
                ""
    in
    String.concat
        [ case s of
            [] ->
                String.concat
                    [ here ]

            Bias_Shift :: t ->
                String.concat
                    [ leftParen
                    , negShift
                    , dotLocus_ True t
                    , rightParen
                    ]

            (Bias_Mul2L j) :: t ->
                String.concat
                    [ leftParen
                    , dotLocusOp_ True (j :: t)
                    , negMul2
                    , hole
                    , rightParen
                    ]

            (Bias_Mul2R j) :: t ->
                String.concat
                    [ leftParen
                    , hole
                    , negMul2
                    , dotLocusOp_ True (j :: t)
                    , rightParen
                    ]

            (Bias_Add2L j) :: t ->
                String.concat
                    [ leftParen
                    , dotLocusOp_ True (j :: t)
                    , negAdd2
                    , hole
                    , rightParen
                    ]

            (Bias_Add2R j) :: t ->
                String.concat
                    [ leftParen
                    , hole
                    , negAdd2
                    , dotLocusOp_ True (j :: t)
                    , rightParen
                    ]
        ]


netToDot : Net -> String
netToDot net =
    let
        color agent =
            case agent.principal of
                Just s ->
                    if polarity s then
                        "\"" ++ opponentColor ++ "\""

                    else
                        "\"" ++ proponentColor ++ "\""

                Nothing ->
                    "\"" ++ proponentColor ++ "\""

        node s =
            "\"" ++ dotLocus s ++ "\""

        node_ s =
            "\"_" ++ dotLocus s ++ "_\""

        maybeNode ms =
            ms
                |> Maybe.map node
                |> Maybe.withDefault "top"

        maybeNode_ ms =
            ms
                |> Maybe.map node_
                |> Maybe.withDefault "top"

        nodes ss =
            "{" ++ String.join ", " (List.map node ss) ++ "}"

        active =
            [ maybeNode_ net.active.principal ++ " [shape = triangle, label = \"\", style = filled, color = " ++ color net.active ++ "]"
            , maybeNode_ net.active.principal ++ " -> " ++ nodes net.active.auxiliary ++ " [headport = n, tailport = s, arrowhead = none]"
            ]

        passive agent =
            [ maybeNode agent.principal ++ " [shape = plaintext, width = 0.02, height = 0.02, margin = 0.02]"
            , maybeNode_ agent.principal ++ " [shape = triangle, label = \"\", style = filled, color = " ++ color agent ++ "]"
            , maybeNode agent.principal ++ " -> " ++ maybeNode_ agent.principal ++ " [headport = n, tailport = s, arrowhead = none]"
            , maybeNode_ agent.principal ++ " -> " ++ nodes agent.auxiliary ++ " [headport = n, tailport = s, arrowhead = none]"
            ]

        options =
            []

        lines =
            List.map ((++) "    ") (options ++ active ++ List.concatMap passive net.passive)
    in
    "digraph {\n" ++ String.join "\n" lines ++ "\n}"



--


type DesignPositive
    = DesignPositive ( Action, DesignNegative )


type DesignNegative
    = DesignNegative (List ( Action, DesignPositive ))


advanceDesignPositive : Action -> DesignPositive -> Maybe DesignNegative
advanceDesignPositive m (DesignPositive ( n, dn )) =
    if m == n then
        Just dn

    else
        Nothing


advanceDesignNegative : Action -> DesignNegative -> Maybe DesignPositive
advanceDesignNegative m (DesignNegative dn_) =
    listLookup m dn_


runDesignPositive : Dispute -> DesignPositive -> Maybe Action
runDesignPositive v ((DesignPositive ( m, _ )) as dp) =
    case v of
        [] ->
            Just m

        n :: w ->
            advanceDesignPositive n dp
                |> Maybe.andThen (runDesignNegative w)


runDesignNegative : Dispute -> DesignNegative -> Maybe Action
runDesignNegative v dn =
    case v of
        [] ->
            Nothing

        n :: w ->
            advanceDesignNegative n dn
                |> Maybe.andThen (runDesignPositive w)


dispute : DesignPositive -> DesignNegative -> Formula -> Dispute
dispute dp dn a =
    let
        go d =
            case
                if modBy 2 (List.length d) == 0 then
                    runDesignPositive (chronicle d a) dp

                else
                    runDesignNegative (chronicle d a) dn
            of
                Just m ->
                    case advanceDispute m d a of
                        Just e ->
                            go e

                        Nothing ->
                            d

                Nothing ->
                    d
    in
    go initialDispute



--


end : DesignNegative
end =
    DesignNegative []


arrow : Formula -> Formula -> Formula
arrow a b =
    Shift (Mul2 a (Shift b))


bool : Formula
bool =
    Add2 Mul0 Mul0


true : Pattern
true =
    Pattern_Add2L Pattern_Mul0


false : Pattern
false =
    Pattern_Add2R Pattern_Mul0


not_ : Locus -> List ( Action, DesignPositive )
not_ s =
    [ ( ( s ++ [], Pattern_Mul2 true Pattern_Shift )
      , DesignPositive
            ( ( s ++ [ Bias_Mul2R Bias_Shift ], false )
            , end
            )
      )
    , ( ( s ++ [], Pattern_Mul2 false Pattern_Shift )
      , DesignPositive
            ( ( s ++ [ Bias_Mul2R Bias_Shift ], true )
            , end
            )
      )
    ]


compose_ : Locus -> List ( Action, DesignPositive )
compose_ s =
    [ ( ( s ++ [], Pattern_Mul2 (Pattern_Mul2 Pattern_Shift Pattern_Shift) Pattern_Shift )
      , let
            f =
                s ++ [ Bias_Mul2L (Bias_Mul2L Bias_Shift) ]

            g =
                s ++ [ Bias_Mul2L (Bias_Mul2R Bias_Shift) ]

            r0 =
                s ++ [ Bias_Mul2R Bias_Shift ]

            eta k =
                DesignNegative
                    (List.concat
                        [ k true
                        , k false
                        ]
                    )
        in
        DesignPositive
            ( ( r0, Pattern_Shift )
            , eta
                (\b0 ->
                    [ ( ( r0 ++ [ Bias_Shift ], Pattern_Mul2 b0 Pattern_Shift )
                      , let
                            r1 =
                                r0 ++ [ Bias_Shift, Bias_Mul2R Bias_Shift ]
                        in
                        DesignPositive
                            ( ( f, Pattern_Mul2 b0 Pattern_Shift )
                            , eta
                                (\b1 ->
                                    [ ( ( f ++ [ Bias_Mul2R Bias_Shift ], b1 )
                                      , DesignPositive
                                            ( ( g, Pattern_Mul2 b1 Pattern_Shift )
                                            , eta
                                                (\b2 ->
                                                    [ ( ( g ++ [ Bias_Mul2R Bias_Shift ], b2 )
                                                      , DesignPositive
                                                            ( ( r1, b2 )
                                                            , end
                                                            )
                                                      )
                                                    ]
                                                )
                                            )
                                      )
                                    ]
                                )
                            )
                      )
                    ]
                )
            )
      )
    ]


compose : DesignPositive
compose =
    DesignPositive
        ( ( [], Pattern_Shift )
        , DesignNegative
            (compose_ [ Bias_Shift ])
        )


compose_test : DesignNegative
compose_test =
    DesignNegative
        [ ( ( [], Pattern_Shift )
          , DesignPositive
                ( ( [ Bias_Shift ], Pattern_Mul2 (Pattern_Mul2 Pattern_Shift Pattern_Shift) Pattern_Shift )
                , DesignNegative
                    (List.concat
                        [ not_ [ Bias_Shift, Bias_Mul2L (Bias_Mul2L Bias_Shift) ]
                        , not_ [ Bias_Shift, Bias_Mul2L (Bias_Mul2R Bias_Shift) ]
                        , [ ( ( [ Bias_Shift, Bias_Mul2R Bias_Shift ], Pattern_Shift )
                            , DesignPositive
                                ( ( [ Bias_Shift, Bias_Mul2R Bias_Shift, Bias_Shift ], Pattern_Mul2 true Pattern_Shift )
                                , end
                                )
                            )
                          ]
                        ]
                    )
                )
          )
        ]



--


listUnsnoc : List a -> Maybe ( List a, a )
listUnsnoc xs =
    case List.reverse xs of
        [] ->
            Nothing

        x :: reversed_init ->
            Just ( List.reverse reversed_init, x )


listLookup : a -> List ( a, b ) -> Maybe b
listLookup k xys =
    case xys of
        [] ->
            Nothing

        ( x, y ) :: xys_ ->
            if k == x then
                Just y

            else
                listLookup k xys_



--


main : Program () Model Msg
main =
    Browser.element
        { init = init
        , update = update
        , subscriptions = subscriptions
        , view = view
        }


port graphvizInit : String -> Cmd msg


port graphvizUpdate : () -> Cmd msg


type alias Model =
    { designPositive : DesignPositive
    , designNegative : DesignNegative
    , formula : Formula
    , step : Int
    }


init : () -> ( Model, Cmd Msg )
init () =
    ( { designPositive = compose
      , designNegative = compose_test
      , formula = arrow (Mul2 (arrow bool bool) (arrow bool bool)) (arrow bool bool)
      , step = 0
      }
    , graphvizInit (netToDot initialNet)
    )


type Msg
    = Forward
    | Backward


update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
    case msg of
        Forward ->
            ( { model
                | step = Basics.min (List.length (dispute model.designPositive model.designNegative model.formula)) (model.step + 1)
              }
            , graphvizUpdate ()
            )

        Backward ->
            ( { model
                | step = Basics.max 0 (model.step - 1)
              }
            , graphvizUpdate ()
            )


subscriptions : Model -> Sub Msg
subscriptions _ =
    Sub.none


view : Model -> Html Msg
view model =
    viewGame model.designPositive model.designNegative model.formula model.step



--


proponentColor =
    "#AA0000"


opponentColor =
    "#0000AA"


posShift =
    "↓"


posMul2 =
    "⊗"


posMul0 =
    "1"


posAdd2 =
    "⊕"


posAdd0 =
    "0"


negShift =
    "↑"


negMul2 =
    "⅋"


negMul0 =
    "⊥"


negAdd2 =
    "&"


negAdd0 =
    "⊤"


hole =
    "_"


here =
    "◯"


viewFormula : Formula -> Html msg
viewFormula =
    viewFormula_ False


viewFormula_ : Bool -> Formula -> Html msg
viewFormula_ parenthesize a =
    let
        attrs =
            [ style "color" proponentColor ]

        -- []
        leftParen =
            if parenthesize then
                text "("

            else
                text ""

        rightParen =
            if parenthesize then
                text ")"

            else
                text ""
    in
    case a of
        Shift b ->
            span
                attrs
                [ leftParen
                , text posShift
                , viewFormulaOp_ True b
                , rightParen
                ]

        Mul2 b c ->
            span
                attrs
                [ leftParen
                , viewFormula_ True b
                , text posMul2
                , viewFormula_ True c
                , rightParen
                ]

        Mul0 ->
            span
                attrs
                [ text posMul0 ]

        Add2 b c ->
            span
                attrs
                [ leftParen
                , viewFormula_ True b
                , text posAdd2
                , viewFormula_ True c
                , rightParen
                ]

        Add0 ->
            span
                attrs
                [ text posAdd0 ]


viewFormulaOp : Formula -> Html msg
viewFormulaOp =
    viewFormulaOp_ False


viewFormulaOp_ : Bool -> Formula -> Html msg
viewFormulaOp_ parenthesize a =
    let
        attrs =
            [ style "color" opponentColor ]

        -- []
        leftParen =
            if parenthesize then
                text "("

            else
                text ""

        rightParen =
            if parenthesize then
                text ")"

            else
                text ""
    in
    case a of
        Shift b ->
            span
                attrs
                [ leftParen
                , text negShift
                , viewFormula_ True b
                , rightParen
                ]

        Mul2 b c ->
            span
                attrs
                [ leftParen
                , viewFormulaOp_ True b
                , text negMul2
                , viewFormulaOp_ True c
                , rightParen
                ]

        Mul0 ->
            span
                attrs
                [ text negMul0 ]

        Add2 b c ->
            span
                attrs
                [ leftParen
                , viewFormulaOp_ True b
                , text negAdd2
                , viewFormulaOp_ True c
                , rightParen
                ]

        Add0 ->
            span
                attrs
                [ text negAdd0 ]


viewLocus : Locus -> Html msg
viewLocus =
    viewLocus_ False


viewLocus_ : Bool -> Locus -> Html msg
viewLocus_ parenthesize s =
    let
        attrs =
            [ style "color" proponentColor ]

        -- []
        leftParen =
            if parenthesize then
                text "("

            else
                text ""

        rightParen =
            if parenthesize then
                text ")"

            else
                text ""
    in
    case s of
        [] ->
            span
                attrs
                [ text here ]

        Bias_Shift :: t ->
            span
                attrs
                [ leftParen
                , text posShift
                , viewLocusOp_ True t
                , rightParen
                ]

        (Bias_Mul2L j) :: t ->
            span
                attrs
                [ leftParen
                , viewLocus_ True (j :: t)
                , text posMul2
                , text hole
                , rightParen
                ]

        (Bias_Mul2R j) :: t ->
            span
                attrs
                [ leftParen
                , text hole
                , text posMul2
                , viewLocus_ True (j :: t)
                , rightParen
                ]

        (Bias_Add2L j) :: t ->
            span
                attrs
                [ leftParen
                , viewLocus_ True (j :: t)
                , text posAdd2
                , text hole
                , rightParen
                ]

        (Bias_Add2R j) :: t ->
            span
                attrs
                [ leftParen
                , text hole
                , text posAdd2
                , viewLocus_ True (j :: t)
                , rightParen
                ]


viewLocusOp_ : Bool -> Locus -> Html msg
viewLocusOp_ parenthesize s =
    let
        attrs =
            [ style "color" opponentColor ]

        -- []
        leftParen =
            if parenthesize then
                text "("

            else
                text ""

        rightParen =
            if parenthesize then
                text ")"

            else
                text ""
    in
    case s of
        [] ->
            span
                attrs
                [ text here ]

        Bias_Shift :: t ->
            span
                attrs
                [ leftParen
                , text negShift
                , viewLocus_ True t
                , rightParen
                ]

        (Bias_Mul2L j) :: t ->
            span
                attrs
                [ leftParen
                , viewLocusOp_ True (j :: t)
                , text negMul2
                , text hole
                , rightParen
                ]

        (Bias_Mul2R j) :: t ->
            span
                attrs
                [ leftParen
                , text hole
                , text negMul2
                , viewLocusOp_ True (j :: t)
                , rightParen
                ]

        (Bias_Add2L j) :: t ->
            span
                attrs
                [ leftParen
                , viewLocusOp_ True (j :: t)
                , text negAdd2
                , text hole
                , rightParen
                ]

        (Bias_Add2R j) :: t ->
            span
                attrs
                [ leftParen
                , text hole
                , text negAdd2
                , viewLocusOp_ True (j :: t)
                , rightParen
                ]


viewPattern : Pattern -> Html msg
viewPattern p =
    let
        attrs =
            []
    in
    case p of
        Pattern_Shift ->
            span
                attrs
                [ text "_" ]

        Pattern_Mul2 q r ->
            span
                attrs
                [ text "("
                , viewPattern q
                , text ","
                , viewPattern r
                , text ")"
                ]

        Pattern_Mul0 ->
            span
                attrs
                [ text "("
                , text ")"
                ]

        Pattern_Add2L q ->
            span
                attrs
                [ text "L("
                , viewPattern q
                , text ")"
                ]

        Pattern_Add2R q ->
            span
                attrs
                [ text "R("
                , viewPattern q
                , text ")"
                ]


viewAction : Action -> Html msg
viewAction ( s, p ) =
    if polarity s then
        div []
            [ viewLocus s
            , text " : "
            , span
                [ style "color" proponentColor ]
                [ viewPattern p ]
            ]

    else
        div []
            [ span
                [ style "color" opponentColor ]
                [ viewPattern p ]
            , text " : "
            , viewLocus s
            ]


viewActionInDispute : Action -> Html msg
viewActionInDispute ( s, p ) =
    if polarity s then
        div
            [ style "text-align" "left" ]
            [ viewLocus s
            , text " : "
            , span
                [ style "color" proponentColor ]
                [ viewPattern p ]
            ]

    else
        div
            [ style "text-align" "right" ]
            [ span
                [ style "color" opponentColor ]
                [ viewPattern p ]
            , text " : "
            , viewLocus s
            ]


viewDesignPositive : DesignPositive -> Html msg
viewDesignPositive (DesignPositive ( m, dn )) =
    div
        [ style "margin" "0 10px"
        , style "width" "max-content"
        ]
        [ div []
            [ viewDesignNegative dn ]
        , div
            [ style "text-align" "center" ]
            [ viewAction m ]
        ]


viewDesignNegative : DesignNegative -> Html msg
viewDesignNegative (DesignNegative dn_) =
    div
        [ style "border-bottom" "1px solid black"
        , style "display" "flex"
        , style "justify-content" "center"
        , style "margin" "0 10px"
        , style "width" "max-content"
        ]
        (List.map
            (\( m, dp ) ->
                div []
                    [ div []
                        [ viewDesignPositive dp ]
                    , div
                        [ style "text-align" "center" ]
                        [ viewAction m ]
                    ]
            )
            dn_
        )


viewDispute : Dispute -> Html msg
viewDispute d =
    div [] (List.map viewActionInDispute d)


viewNet : Dispute -> Int -> Html Msg
viewNet d n =
    let
        btn msg label =
            button
                [ onClick msg
                , style "border" "1px solid black"
                , style "margin-right" "10px"
                , style "padding" "10px"
                ]
                [ text label ]
    in
    div
        []
        [ btn Backward "< step backward"
        , btn Forward "step forward >"
        , if modBy 2 n == 0 then
            div
                [ style "margin" "10px 0"
                , style "color" proponentColor
                ]
                [ text "Proponent's move" ]

          else
            div
                [ style "margin" "10px 0"
                , style "color" opponentColor
                ]
                [ text "Opponent's move" ]
        , div
            [ id "graphviz"
            , attribute "data-dot" (netToDot (disputeToNet (List.take n d)))
            , style "margin-top" "10px"
            , style "display" "flex"
            , style "align-items" "center"
            , style "justify-content" "center"
            ]
            []
        ]


viewGame : DesignPositive -> DesignNegative -> Formula -> Int -> Html Msg
viewGame dp dn a n =
    let
        d =
            dispute dp dn a

        box title contents =
            div
                [ style "border" "1px solid black"
                , style "margin" "10px"
                , style "padding" "10px"
                ]
                [ h2
                    [ style "font-weight" "bold"
                    , style "margin-bottom" "10px"
                    ]
                    [ text title ]
                , div
                    [ style "overflow" "scroll"
                    , style "text-align" "center"
                    ]
                    [ contents ]
                ]
    in
    div
        []
        [ box "Visualization" (viewNet d n)
        , box "Arena" (viewFormula a)
        , box "Play" (viewDispute d)
        , box "Proponent Strategy" (viewDesignPositive dp)
        , box "Opponent Strategy" (viewDesignNegative dn)
        ]
